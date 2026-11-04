/-
Copyright (c) 2026 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/

module

import all LeanFmt.Config
import all LeanFmt.Doc

import Lean.Parser.Command

/-! Blank lines between the items of a list: structure fields, inductive constructors, `match` or
`cases`/`induction` alternatives, the elements of a `do` block, and the tactics of a tactic block
(`blank-lines-between-*`).

This is a pass over the rendered module rather than a boundary in the layout because one of its
questions is a layout outcome. Whether an item spans several rows is decided by the renderer, and a
`Std.Format` separator cannot depend on whether its neighbour broke. The other questions are source
facts: whether the source wrote a blank line between two items, and whether an item carries a doc
comment or an attribute.

Each formatted command is parsed again under the context Lean parsed the original under, and only a
command that is structurally equal to its source takes part, so the two have the same lists with the
same items in the same order. A list is a node whose children, two or more, are all items of one
family, or the tactics of a tactic block, which alternate with their separators. The pass then rewrites only the gap above each item after the first: its leading blank rows
become one or none, and everything else in it stays. What remains in a gap is the item's own comments,
which is why a blank line goes above them and why they count toward the item.

`grouped` also compares the kinds of two neighbouring items, which only `do` elements have in a
sense worth reading: every `let` form is one kind, a reassignment another, and an expression is the
function it calls. `compact-block-size` exempts a short `do` or tactic block from every blank line
the spacing would add, since a block of two or three elements reads as one step.

A command that does not reparse to its source is left as rendered. Nothing here can make that
happen, since a blank row is never a token, and the validator refuses such a command on its own
terms. -/

namespace LeanFmt.Internal.Formatter.BlankLines

/-- One formatted command: the syntax Lean parsed, the context it parsed it under, and the source
range its mark in the rendered module covers. -/
structure Command where
  source : Lean.Syntax
  context : Lean.Parser.ParserModuleContext
  unit : SourceRange

private inductive Family where
  | fields
  | constructors
  | alternatives
  | doElements
  | tactics
  deriving BEq, Inhabited

private def family? : Lean.Name → Option Family
  | ``Lean.Parser.Command.structExplicitBinder | ``Lean.Parser.Command.structImplicitBinder |
    ``Lean.Parser.Command.structInstBinder | ``Lean.Parser.Command.structSimpleBinder =>
    some .fields
  | ``Lean.Parser.Command.ctor => some .constructors
  | ``Lean.Parser.Term.matchAlt | ``Lean.Parser.Tactic.inductionAlt => some .alternatives
  | ``Lean.Parser.Term.doSeqItem => some .doElements
  | _ => none

private def Family.spacing (format : FormatConfig) : Family → ElementSpacing
  | .fields => format.blankLinesBetweenFields
  | .constructors => format.blankLinesBetweenConstructors
  | .alternatives => format.blankLinesBetweenAlternatives
  | .doElements => format.blankLinesBetweenDoElements
  | .tactics => format.blankLinesBetweenTactics

/-- Whether `compact-block-size` applies: a block of statements, not a declaration's members. -/
private def Family.block : Family → Bool
  | .doElements | .tactics => true
  | _ => false

/-- Whether any list family asks for something other than the layout's own `never`. -/
def enabled (format : FormatConfig) : Bool :=
  [Family.fields, .constructors, .alternatives, .doElements, .tactics].any
    (·.spacing format != .never)

private def first (stx : Lean.Syntax) : Lean.Syntax :=
  if stx.getKind == Lean.choiceKind then stx.getArg 0 else stx

/-- The name a call is grouped by. A qualified name whose first component is lower case is a method
on a local, `budget.snapshot`, and groups by the method alone, so calls on different receivers
group; any other name is a function and groups by its full name, so `IO.println` and
`IO.eprintln` do not. Lean's naming convention is what tells the two apart, since the syntax
alone cannot. -/
private def calleeName (name : Lean.Name) : String :=
  match name.eraseMacroScopes.components with
  | receiver@(.str _ head) :: _ :: _ =>
    if head.front.isLower then (name.eraseMacroScopes.components.getLast?.getD receiver).toString
    else name.eraseMacroScopes.toString
  | _ => name.eraseMacroScopes.toString

/-- What an expression calls: the function of an application, seen through `<|`, `$`, `|>`,
parentheses and method projections, so `throw <| e` calls `throw` and `x |>.push y` calls `push`.
Anything else is its own syntax kind. -/
private partial def callee (term : Lean.Syntax) : String :=
  let term := first term
  if term.isIdent then calleeName term.getId
  else
    match term.getKind with
    | ``Lean.Parser.Term.app | `«term_<|_» | `«term_$__» => callee (term.getArg 0)
    | `«term_|>_» => callee (term.getArg 2)
    | ``Lean.Parser.Term.paren => callee (term.getArg 1)
    | kind@``Lean.Parser.Term.proj | kind@``Lean.Parser.Term.pipeProj =>
      let field := term.getArg 2
      if field.isIdent then field.getId.eraseMacroScopes.toString else kind.toString
    | kind => kind.toString

/-- The kind `grouped` compares two `do` elements by. Every `let` form is one kind and every
reassignment another, so a run of bindings stays together and a mutation stands apart from them;
an expression is the function it calls. -/
private def doElementKind (item : Lean.Syntax) : String :=
  let element := first (item.getArg 0)
  match element.getKind with
  | ``Lean.Parser.Term.doLet | ``Lean.Parser.Term.doLetElse | ``Lean.Parser.Term.doLetArrow |
    ``Lean.Parser.Term.doLetRec => "let"
  | ``Lean.Parser.Term.doReassign | ``Lean.Parser.Term.doReassignArrow => "reassign"
  | ``Lean.Parser.Term.doExpr => "call " ++ callee (element.getArg 0)
  | kind => kind.toString

private def Family.kind (family : Family) (item : Lean.Syntax) : String :=
  match family with
  | .doElements => doElementKind item
  | _ => (first item).getKind.toString

/-- One list, its items paired by position, and where the token in front of its first item ends in
the output: the first item's gap starts there. -/
private structure List where
  family : Family
  source : Array Lean.Syntax
  output : Array Lean.Syntax
  openerStop : Nat

private structure Walk where
  lists : Array List := #[]
  /-- The end of the last output token visited, in preorder. -/
  lastStop : Nat := 0

/-- The tactics of a tactic block, as a list. Separators sit between the tactics in one node, `;` or
an empty node for a line break, so the tactics are its even children. A bracketed block's first gap
starts after its `{`; an indented block's after whatever token precedes it. -/
private def tacticList? (source output : Lean.Syntax) (lastStop : Nat) : Option List := do
  let bracketed := output.getKind == ``Lean.Parser.Tactic.tacticSeqBracketed
  guard (bracketed || output.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented)
  let index := if bracketed then 1 else 0
  let openerStop :=
    if bracketed then ((output.getArg 0).getTailPos?.map (·.byteIdx)).getD lastStop else lastStop
  let tactics (block : Lean.Syntax) : Array Lean.Syntax :=
    let items := (block.getArg index).getArgs
    (List.range ((items.size + 1) / 2)).toArray.map fun position => items[2 * position]!
  let output := tactics output
  guard (output.size ≥ 2)
  return { family := .tactics, source := tactics source, output, openerStop }

private def family?OfList (args : Array Lean.Syntax) : Option Family := do
  guard (args.size ≥ 2)
  let first ← family? args[0]!.getKind
  guard (args.all fun arg => family? arg.getKind == some first)
  return first

/-- Every list in a command, walking the source and its structurally equal output together. Only
the first alternative of a `choice` is read: the two trees agree on every alternative, and only one
spells the bytes. -/
private partial def walk (source output : Lean.Syntax) (state : Walk) : Walk :=
  match source, output with
  | .node _ kind sourceArgs, .node _ _ outputArgs =>
    let state :=
      if kind == Lean.nullKind then
        match family?OfList outputArgs with
        | some family =>
          { state with
            lists :=
              state.lists.push
                { family, source := sourceArgs, output := outputArgs,
                  openerStop := state.lastStop } }
        | none => state
      else
        match tacticList? source output state.lastStop with
        | some list => { state with lists := state.lists.push list }
        | none => state
    let count := if kind == Lean.choiceKind then min 1 sourceArgs.size else sourceArgs.size
    (List.range count).foldl (init := state) fun state index =>
      walk (sourceArgs[index]?.getD .missing) (outputArgs[index]?.getD .missing) state
  | _, .atom .. | _, .ident .. =>
    match output.getTailPos? with
    | some stop => { state with lastStop := stop.byteIdx }
    | none => state
  | _, _ => state

/-- Whether an item carries a doc comment or an attribute. A constructor's doc comment sits in front
of its `|`; every other one is in the item's `declModifiers`. -/
private def modified (item : Lean.Syntax) : Bool :=
  let leadingDoc := item.getKind == ``Lean.Parser.Command.ctor && (item.getArg 0).getNumArgs > 0
  let modifiers :=
    item.getArgs.any fun arg =>
      arg.getKind == ``Lean.Parser.Command.declModifiers &&
        ((arg.getArg 0).getNumArgs > 0 || (arg.getArg 1).getNumArgs > 0)
  leadingDoc || modifiers

/-- The byte offset at which every row of `text` starts. -/
private def rowStarts (bytes : ByteArray) : Array Nat :=
  Id.run do
    let mut starts := #[0]
    for index in [0:bytes.size] do
      if bytes[index]! == 10 then
        starts := starts.push (index + 1)
    return starts

/-- The row a byte offset is on. -/
private def rowOf (starts : Array Nat) (offset : Nat) : Nat :=
  Id.run do
    let mut low := 0
    let mut high := starts.size
    while low + 1 < high do
      let middle := (low + high) / 2
      if starts[middle]! ≤ offset then
        low := middle
      else
        high := middle
    return low

private def slice (bytes : ByteArray) (start stop : Nat) : String :=
  (String.fromUTF8? (bytes.extract start stop)).getD ""

private def blankRow (bytes : ByteArray) (starts : Array Nat) (row : Nat) : Bool :=
  let stop := starts[row + 1]?.getD bytes.size
  (slice bytes starts[row]! stop).trimAscii.isEmpty

/-- Whether the source has a whitespace-only row between two offsets. -/
private def blankBetween (source : ByteArray) (stop start : Nat) : Bool :=
  let rows := (slice source stop start).splitOn "\n"
  (rows.drop 1).dropLast.any (·.trimAscii.isEmpty)

/-- One replacement in the rendered text. -/
private structure Edit where
  start : Nat
  stop : Nat
  replacement : String

/-- The rows strictly between the one `stop` ends on and the one `item` starts on. -/
private structure Gap where
  firstRow : Nat
  /-- One past the last row; equal to `firstRow` when the item starts the row after. -/
  stopRow : Nat
  /-- Whether a comment is in the gap: it belongs to the item below it. -/
  commented : Bool

private def gap? (bytes : ByteArray) (starts : Array Nat) (stop : Nat) (item : Lean.Syntax) :
    Option Gap := do
  let start ← item.getPos?
  let previousRow := rowOf starts stop
  let itemRow := rowOf starts start.byteIdx
  guard (previousRow < itemRow)
  -- An item that does not open its own row has no gap to rewrite.
  guard (slice bytes starts[itemRow]! start.byteIdx).trimAscii.isEmpty
  let firstRow := previousRow + 1
  let commented :=
    (List.range (itemRow - firstRow)).any fun offset => !blankRow bytes starts (firstRow + offset)
  return { firstRow, stopRow := itemRow, commented }

/-- How one sequence of items is spaced: the configured value, whether it is a block short enough
that the value adds nothing, and the kind `grouped` compares items by. -/
private structure Policy where
  spacing : ElementSpacing
  compact : Bool
  kind : Lean.Syntax → String

/-- The edits one sequence of items asks for. `openerStop` is where the token in front of the first
item ends, when there is one: the first item's comments are in the gap after it. -/
private def sequenceEdits (policy : Policy) (sourceBytes bytes : ByteArray) (starts : Array Nat)
    (source output : Array Lean.Syntax) (openerStop : Option Nat) : Array Edit :=
  Id.run do
    let gaps : Array (Option Gap) :=
      (List.range output.size).toArray.map fun index =>
        let stop :=
          if index == 0 then openerStop else (output[index - 1]!.getTailPos?).map (·.byteIdx)
        stop.bind fun stop => gap? bytes starts stop output[index]!
    let commented (index : Nat) : Bool := (gaps[index]!).any (·.commented)
    let annotated (index : Nat) : Bool := commented index || modified output[index]!
    let multiline (index : Nat) : Bool :=
      commented index ||
        match output[index]!.getPos?, output[index]!.getTailPos? with
        | some start, some stop => rowOf starts start.byteIdx != rowOf starts stop.byteIdx
        | _, _ => false
    let mut edits := #[]
    for index in [1:output.size] do
      let some gap := gaps[index]! | continue
      let authored :=
        match source[index - 1]!.getTailPos?, source[index]!.getPos? with
        | some stop, some start => blankBetween sourceBytes stop.byteIdx start.byteIdx
        | _, _ => false
      let around (property : Nat → Bool) := property (index - 1) || property index
      let added :=
        match policy.spacing with
        | .never | .preserve => false
        | .always => true
        | .aroundAnnotated => around annotated
        | .aroundMultiline => around multiline
        | .grouped =>
          around multiline || policy.kind source[index - 1]! != policy.kind source[index]!
      -- `never` removes what the source wrote; every other value keeps it.
      let blank := policy.spacing != .never && (authored || (added && !policy.compact))
      -- Only the blank rows at the top of the gap: one between two of the item's comments is theirs.
      let mut leading := 0
      while
        gap.firstRow + leading < gap.stopRow && blankRow bytes starts (gap.firstRow + leading) do
        leading := leading + 1
      let wanted := if blank then 1 else 0
      unless leading == wanted do
        edits :=
          edits.push
            { start := starts[gap.firstRow]!, stop := starts[gap.firstRow + leading]!
              replacement := if blank then "\n" else "" }
    return edits

/-- Where `offset` moves to once `edits` (sorted, disjoint) are applied. An offset inside an edit
cannot be a mark boundary, since every edit lies strictly inside one command. -/
private def shift (edits : Array Edit) (offset : Nat) : Nat :=
  edits.foldl (init := offset) fun moved edit =>
    if edit.stop ≤ offset then moved + edit.replacement.utf8ByteSize - (edit.stop - edit.start)
    else moved

/-- Apply the configured spacing to a rendered module. `source` is the normalized source the
commands were parsed from; `commands` are the commands laid out natively, so a command emitted
as its own bytes is never respaced. -/
def apply (format : FormatConfig) (source : String) (rendered : Rendered)
    (commands : Array Command) : Rendered :=
  Id.run do
    let bytes := rendered.text.toUTF8
    let sourceBytes := source.toUTF8
    let starts := rowStarts bytes
    let input := Lean.Parser.mkInputContext rendered.text "<candidate>"
    let mut edits : Array Edit := #[]
    -- Marks and commands are both in source order, so one cursor finds every command's mark.
    let mut markIndex := 0
    for command in commands do
      let mut probe := markIndex
      while h : probe < rendered.sourceMap.size do
        if rendered.sourceMap[probe].source == command.unit then
          break
        probe := probe + 1
      let some mark := rendered.sourceMap[probe]? | continue
      markIndex := probe + 1
      let (output, _, messages) :=
        Lean.Parser.parseCommand input command.context { pos := ⟨mark.output.start⟩ } .empty
      unless !messages.hasErrors && output.structEq command.source do
        continue
      let lists := (walk command.source output { lastStop := mark.output.start }).lists
      for list in lists do
        -- `never` is the layout's own answer, so a family left at it is not touched at all.
        let spacing := list.family.spacing format
        if spacing == .never then
          continue
        let policy : Policy :=
          { spacing, kind := list.family.kind
            compact := list.family.block && list.output.size ≤ format.compactBlockSize }
        for edit in
          sequenceEdits policy sourceBytes bytes starts list.source list.output
            (some list.openerStop) do
          if mark.output.start < edit.start && edit.stop < mark.output.stop then
            edits := edits.push edit
    if edits.isEmpty then
      return rendered
    -- Two lists never share a gap, since an inner list's gaps are rows inside one outer item, so
    -- the overlap check only guards that argument; what it drops must not reach `shift` either.
    edits := edits.qsort (·.start < ·.start)
    let mut applied : Array Edit := #[]
    let mut text := ""
    let mut cursor := 0
    for edit in edits do
      if edit.start < cursor then
        continue
      text := text ++ slice bytes cursor edit.start ++ edit.replacement
      cursor := edit.stop
      applied := applied.push edit
    text := text ++ slice bytes cursor bytes.size
    let sourceMap :=
      rendered.sourceMap.map fun mark =>
        { mark with output := ⟨shift applied mark.output.start, shift applied mark.output.stop⟩ }
    return { rendered with
        text, sourceMap }

end LeanFmt.Internal.Formatter.BlankLines
