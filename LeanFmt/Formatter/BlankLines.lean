/-
Copyright (c) 2026 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/

module

import all LeanFmt.Config
import all LeanFmt.Doc

import Lean.Parser.Command

/-! Blank lines between the items of a list: structure fields, inductive constructors, and `match`
or `cases`/`induction` alternatives (`blank-lines-between-*`).

This is a pass over the rendered module rather than a boundary in the layout because one of its
questions is a layout outcome. Whether an item spans several rows is decided by the renderer, and a
`Std.Format` separator cannot depend on whether its neighbour broke. The other questions are source
facts: whether the source wrote a blank line between two items, and whether an item carries a doc
comment or an attribute.

Each formatted command is parsed again under the context Lean parsed the original under, and only a
command that is structurally equal to its source takes part, so the two have the same lists with the
same items in the same order. A list is a node whose children, two or more, are all items of one
family. The pass then rewrites only the gap above each item after the first: its leading blank rows
become one or none, and everything else in it stays. What remains in a gap is the item's own comments,
which is why a blank line goes above them and why they count toward the item.

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
  deriving BEq, Inhabited

private def family? (kind : Lean.Name) : Option Family :=
  if
      kind == ``Lean.Parser.Command.structExplicitBinder ||
        kind == ``Lean.Parser.Command.structImplicitBinder ||
        kind == ``Lean.Parser.Command.structInstBinder ||
        kind == ``Lean.Parser.Command.structSimpleBinder then
    some .fields
  else
    if kind == ``Lean.Parser.Command.ctor then some .constructors
    else
      if kind == ``Lean.Parser.Term.matchAlt || kind == ``Lean.Parser.Tactic.inductionAlt then
        some .alternatives
      else none

private def Family.spacing (format : FormatConfig) : Family → ElementSpacing
  | .fields => format.blankLinesBetweenFields
  | .constructors => format.blankLinesBetweenConstructors
  | .alternatives => format.blankLinesBetweenAlternatives

/-- Whether any list family asks for something other than the layout's own `never`. -/
def enabled (format : FormatConfig) : Bool :=
  [Family.fields, .constructors, .alternatives].any (·.spacing format != .never)

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
      else state
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

/-- The edits one list asks for. -/
private def listEdits (spacing : ElementSpacing) (sourceBytes bytes : ByteArray)
    (starts : Array Nat) (list : List) : Array Edit :=
  Id.run do
    let gaps : Array (Option Gap) :=
      (List.range list.output.size).toArray.map fun index =>
        let stop :=
          if index == 0 then some list.openerStop
          else (list.output[index - 1]!.getTailPos?).map (·.byteIdx)
        stop.bind fun stop => gap? bytes starts stop list.output[index]!
    let commented (index : Nat) : Bool := (gaps[index]!).any (·.commented)
    let annotated (index : Nat) : Bool := commented index || modified list.output[index]!
    let multiline (index : Nat) : Bool :=
      commented index ||
        match list.output[index]!.getPos?, list.output[index]!.getTailPos? with
        | some start, some stop => rowOf starts start.byteIdx != rowOf starts stop.byteIdx
        | _, _ => false
    let mut edits := #[]
    for index in [1:list.output.size] do
      let some gap := gaps[index]! | continue
      let authored :=
        match list.source[index - 1]!.getTailPos?, list.source[index]!.getPos? with
        | some stop, some start => blankBetween sourceBytes stop.byteIdx start.byteIdx
        | _, _ => false
      let blank :=
        match spacing with
        | .never => false
        | .preserve => authored
        | .always => true
        | .aroundAnnotated => authored || annotated (index - 1) || annotated index
        | .aroundMultiline => authored || multiline (index - 1) || multiline index
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
        for edit in listEdits spacing sourceBytes bytes starts list do
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
