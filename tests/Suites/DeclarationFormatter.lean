module

public import Test

import all LeanFmt.Config

/-!
# The declaration-formatter suite

Declaration families use structural groups at widths 20/40/80/100; members, constructors, deriving,
mutual, where, comments, and custom terms preserve order.
-/

open LeanFmt.Test
open LeanFmt.Test.Analyze

namespace DeclarationFormatter

/-- The keyword inventory every width asserted, in the old block's order. `\b` guards become
`wordBoundary` tokens. -/
private def requiredPatterns : Array FlexPattern :=
  #[[.lit "abbrev", .someWs, .lit "VeryLongAliasName"],
    [.lit "opaque", .someWs, .lit "opaqueValue"], [.lit "axiom", .someWs, .lit "assumedValue"],
    [.lit "@[inline]", .someWs, .lit "private", .someWs, .lit "def", .someWs, .lit "modifiedValue"],
    [.lit "«name with spaces»"], [.wordBoundary, .lit "instance", .wordBoundary],
    [.lit "structure", .someWs, .lit "Packet"], [.lit "structure", .someWs, .lit "ExtendedPacket"],
    [.lit "class", .someWs, .lit "HasValue"], [.lit "class", .someWs, .lit "ExtendedHasValue"],
    [.lit "inductive", .someWs, .lit "Choice"], [.lit "coinductive", .someWs, .lit "Always"],
    [.lit "class", .someWs, .lit "inductive", .someWs, .lit "Classified"],
    [.wordBoundary, .lit "mutual", .wordBoundary], [.lit "def", .someWs, .lit "isEven"],
    [.lit "def", .someWs, .lit "isOdd"], [.lit "def", .someWs, .lit "countdown"],
    [.lit "termination_by"], [.lit "def", .someWs, .lit "withLocal"],
    [.lit "def", .someWs, .lit "withLocals"], [.wordBoundary, .lit "where", .wordBoundary]]

/-- Lines starting with the given prefix. A prefix rather than a whole line because the column is
what is asserted and the rest of the row moves with the margin. -/
private def countPrefix (text pfx : String) : Nat :=
  (text.splitOn "\n").filter (·.startsWith pfx) |>.length

/-- Byte position of `needle`'s first occurrence, or none. -/
private def positionOf? (text needle : String) : Option Nat :=
  match text.splitOn needle with
  | head :: _ :: _ => some head.utf8ByteSize
  | _ => none

/-- One Families width: idempotence and the metric invariants, the keyword inventory, the field,
constructor, and mutual orderings, and no trailing whitespace. -/
private def testWidth (root setup : System.FilePath) (application : String) (width : Nat) :
    IO Unit := do
  let report ←
    analyzeExact root application setup "tests/fixtures/declaration-formatter/Families.lean"
        "Families.lean" s!"4:{width}"
  let (canonical, text) ← canonical report s!"width {width}"
  ensure
      (natAt? canonical [.field "metrics", .field "nativeDocuments"] ==
        natAt? canonical [.field "metrics", .field "commands"])
      s!"width {width}: nativeDocuments ≠ commands"
  let aligned := (natAt? canonical [.field "metrics", .field "alignedTokens"]).getD 0
  let commands := (natAt? canonical [.field "metrics", .field "commands"]).getD 0
  ensure (aligned > commands) s!"width {width}: alignedTokens stopped dominating commands"
  for pattern in requiredPatterns do
    ensureFlex s!"width {width}" text pattern
  match ["first : α", "second : α", "count : Nat"].map (positionOf? text) |>.toArray with
  | #[some first, some second, some count] =>
    ensure (first < second && second < count) s!"width {width}: structure fields reordered"
  | _ =>
    throw <| IO.userError s!"width {width}: structure fields missing"
  let constructorPatterns : Array FlexPattern :=
    #[[.lit "|", .someWs, .lit "neither"], [.lit "|", .someWs, .lit "left"],
      [.lit "|", .someWs, .lit "right"]]
  match constructorPatterns.map (flexFind? text) with
  | #[some neither, some left, some right] =>
    ensure (neither < left && left < right) s!"width {width}: constructors reordered"
  | _ =>
    throw <| IO.userError s!"width {width}: constructors missing"
  match flexFind? text [.lit "def", .someWs, .lit "isEven"],
    flexFind? text [.lit "def", .someWs, .lit "isOdd"] with
  | some isEven, some isOdd =>
    ensure (isEven < isOdd) s!"width {width}: mutual definitions reordered"
  | _, _ =>
    throw <| IO.userError s!"width {width}: mutual definitions missing"
  -- `Term.whereDecls` items land at the list's own column, and the multi-item form lands where the
  -- single-item form already did. `sepByIndent` spells its first item after a forced `align` and
  -- every later one after a `text "\n"`, then wraps each in a `ppGroup` whose leading soft `line`
  -- fits and flattens to a space -- so a multi-item clause sat one column right of a single-item
  -- one, and right of its own docstring, until `dropLeadingBreak`. The offending space is a
  -- flattened `line`, so the column it produced did not move with the margin: asserted at every
  -- width because width is exactly what it was independent of.
  for binding in ["  first (n : Nat) :", "  second (n : Nat) :"] do
    ensureEq s!"width {width}: a `where` binding left its column" 1 (countPrefix text binding)
  -- The single-item clause hugs the `where` row instead, as `singleField` pins for
  -- `whereStructInst`. Asserted beside the two-item case because that is what makes the two-item
  -- column a claim about `sepByIndent`'s `align` rather than about `where` clauses generally.
  ensureEq s!"width {width}: the lone `where` binding left its own row" 1
      (countPrefix text "where localValue :")
  ensureNoTrailingWhitespace s!"width {width}" text

/-- The narrow-width shapes: the opaque signature and the extending structure break where the old
regexes pinned them. -/
private def testNarrowLayout (root setup : System.FilePath) (application : String) : IO Unit := do
  let narrow ←
    do
      let report ←
        analyzeExact root application setup "tests/fixtures/declaration-formatter/Families.lean"
            "Families.lean" "4:20"
      (·.2) <$> canonical report "width 20"
  ensureFlex "width 20" narrow
      [.lit "opaque", .someWs, .lit "opaqueValue", .someWs, .lit "(first", .someWs, .lit "second",
        .anyWs, .lit ":", .anyWs, .lit "Nat)"]
  ensureFlex "width 20" narrow
      [.lit "structure", .someWs, .lit "ExtendedPacket", .someWs, .lit "(α", .anyWs, .lit ":",
        .anyWs, .lit "Type", .someWs, .lit "u)"]

/-- The wide-width shape: the extending structure stays on one line, and the widths disagree. -/
private def testWideLayout (root setup : System.FilePath) (application : String) : IO Unit := do
  let wide ←
    do
      let report ←
        analyzeExact root application setup "tests/fixtures/declaration-formatter/Families.lean"
            "Families.lean" "4:100"
      (·.2) <$> canonical report "width 100"
  ensureFlex "width 100" wide
      [.lit "structure", .someWs, .lit "ExtendedPacket", .someWs, .lit "(α", .anyWs, .lit ":",
        .anyWs, .lit "Type", .someWs, .lit "u)", .someWs, .lit "extends", .someWs, .lit "Packet",
        .someWs, .lit "α", .someWs, .lit "where"]
  let narrow ←
    do
      let report ←
        analyzeExact root application setup "tests/fixtures/declaration-formatter/Families.lean"
            "Families.lean" "4:20"
      (·.2) <$> canonical report "width 20"
  ensure (narrow ≠ wide) "declaration groups ignored width"

/-- The comments fixture: each payload exactly once. -/
private def testComments (root setup : System.FilePath) (application : String) : IO Unit := do
  let report ←
    analyzeExact root application setup "tests/fixtures/declaration-formatter/Comments.lean"
        "Comments.lean" "4:60"
  let (_, text) ← canonical report "comments"
  for payload in
    ["/-- The declaration payload is exact. -/", "-- trailing body payload",
      "/-- The field payload is exact. -/"] do
    ensure ((text.splitOn payload).length == 2) s!"comments: {payload} does not occur exactly once"

/-- `declaration-body`: the canonical `next-line` default breaks even a short body in both
directions; `same-line` joins when the joined line fits `line-width` — source-flat and
already-broken alike — and breaks exactly as the default when it does not. The bodies live in a
scratch file so the two configurations render the same source through the full config plumbing.

The last two declarations pin the fit measure against the `:=` line's own indentation, one column
either side of the margin. Their `:=` sits at column 4 on a continuation line, so a measure that
drops the leading run rather than counting it reads both as four columns short: the 101-column
`indentedJoinOverflow` measured 97 and joined, and the renderer bought the join back by breaking
the signature it had already fitted. -/
private def testDeclarationBody (root work setup : System.FilePath) (application : String) :
    IO Unit := do
  let fixture := work / "Bodies.lean"
  writeFile fixture
      "module\n\ndef foo := 1\n\ndef bar :=\n  2\n\ndef baz := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) + 1111\n\ndef indentedJoinOverflow (firstArgument secondArgument thirdArgument fourthArgumentXY : Nat) :\n    Nat :=\n  firstArgument + secondArgument + thirdArgument + fourthArgumentXY + 1111111111111111111111\n\ndef indentedJoinExactFit (firstArgument secondArgument thirdArgument fourthArgumentXY : Nat) :\n    Nat :=\n  firstArgument + secondArgument + thirdArgument + fourthArgumentXY + 111111111111111111111\n"
  let canonicalFormat : LeanFmt.Internal.FormatConfig := {}
  let report ←
    analyzeExact root application setup fixture.toString "Bodies.lean"
        s!"4j{(Lean.toJson canonicalFormat).compress}"
  let (_, text) ← canonical report "declaration-body default"
  ensureContains text "def foo :=\n  1" "the default did not keep the canonical body break"
  ensureContains text "def bar :=\n  2" "the default joined an already-broken body"
  let sameLine : LeanFmt.Internal.FormatConfig := { declarationBody := .sameLine }
  let joined ←
    analyzeExact root application setup fixture.toString "Bodies.lean"
        s!"4j{(Lean.toJson sameLine).compress}"
  let (_, joinedText) ← canonical joined "declaration-body same-line"
  ensureContains joinedText "def foo := 1\n" "same-line did not keep a source-flat body flat"
  ensureContains joinedText "def bar := 2\n" "same-line did not join an already-broken body"
  ensureContains joinedText "def baz :=\n  Nat.succ"
      "same-line joined a body whose joined line overflows"
  ensureContains joinedText
      "    Nat :=\n  firstArgument + secondArgument + thirdArgument + \
    fourthArgumentXY + 1111111111111111111111"
      "same-line joined a body whose joined line overflows by the `:=` line's indentation"
  ensureContains joinedText
      "    Nat := firstArgument + secondArgument + thirdArgument + \
    fourthArgumentXY + 111111111111111111111"
      "same-line declined a joined line that fits the margin exactly"
  for line in joinedText.splitOn "\n" do
    ensure (line.length <= 100) s!"same-line put a row over the margin: {line}"

/-- `declaration-where`: the default `same-line` keeps `where` on the signature row whenever the
flattened signature plus `" where"` fits `line-width`, and `next-line` always gives it its own row.
The fixture pins the measure's two edges at 100 and 101 columns, that a doc comment stays out of it,
that a `;`-separated field list still hugs the `where` row, that a lone field keeps the row the
source gave it, and that a return type filling its own continuation row still declines.

Left to the native document, this boundary fires at roughly half the margin whatever the signature
costs -- 49 columns joined and 50 broke at `line-width` 100, 32 and 33 at 60 -- because
`whereStructInst`'s only break sits in a group that measures on through `sepByIndent`'s `align`. So
the join is a repair (LAY-ALIGN-COMPENSATION), not a preference; the gate on it is not, because
`where` cannot always be given a row at all.

Two narrower measures were tried here and both are refused by cases below. A row-shaped one is not
idempotent: `instance [Inhabited α] : Inhabited (α × α) where` at `line-width` 20 declines, the
renderer breaks the signature, the row carrying the last token then fits, and the second pass joins
-- `ValidationGate.idempotence` refuses that file, which is why this suite renders through the full
config plumbing rather than once. Measuring the flattened *return type* is idempotent and buys back
the row the header measure spends on an overflowing signature, but it bounds the final row from
below rather than above: `unbreakableReturnRow` joins under it and renders 103 columns. The header
measure over-measures in the one safe direction, so it stays, and `whereJoinOverflows` pins the
column it costs. -/
private def testDeclarationWhere (root work setup : System.FilePath) (application : String) :
    IO Unit := do
  let fixture := work / "Wheres.lean"
  writeFile fixture
      "module\n\nstructure Packet where\n  first : Nat\n  second : Nat\n\nstructure Single where\n  only : Nat\n\n/-- A doc comment is syntax, not trivia, and must stay out of the fit measure. -/\ndef documented (input : Nat) : Packet where\n  first := input\n  second := input\n\ndef whereJoinFitsExactly (inputXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX : Nat) : Packet where\n  first := 0\n  second := 0\n\ndef whereJoinOverflows (inputXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX : Nat) : Packet where\n  first := 0\n  second := 0\n\ndef semiSeparated (input : Nat) : Packet where\n  first := input; second := input\n\ndef singleField (input : Nat) : Single where\n  only := input\n\nnamespace NamespaceSegmentAlphaGivenAGenerousLongName\nnamespace NamespaceSegmentBetaGivenAGenerousLongNames\n\nstructure Inner where\n  solo : Nat\n\nend NamespaceSegmentBetaGivenAGenerousLongNames\nend NamespaceSegmentAlphaGivenAGenerousLongName\n\ndef unbreakableReturnRow :\n    NamespaceSegmentAlphaGivenAGenerousLongName.NamespaceSegmentBetaGivenAGenerousLongNames.Inner where\n  solo := 0\n"
  let canonicalFormat : LeanFmt.Internal.FormatConfig := {}
  let report ←
    analyzeExact root application setup fixture.toString "Wheres.lean"
        s!"4j{(Lean.toJson canonicalFormat).compress}"
  let (_, text) ← canonical report "declaration-where default"
  ensureContains text "def documented (input : Nat) : Packet where\n  first := input"
      "the default let a doc comment push `where` off the signature row"
  ensureContains text ": Packet where\n  first := 0\n  second := 0\n\ndef whereJoinOverflows"
      "the default broke a `where` whose joined row fits the margin exactly"
  ensureContains text ") : Packet\n    where\n  first := 0\n  second := 0\n\ndef semiSeparated"
      "the default joined a `where` whose joined row is one column over the margin"
  ensureContains text "def semiSeparated (input : Nat) : Packet where first := input;"
      "the default drove a `;`-separated list's first field off the `where` row"
  ensureContains text "def singleField (input : Nat) : Single where\n  only := input"
      "the default pulled a lone field onto the `where` row"
  -- 93 columns of return type: the row it lands on holds it (97) but cannot also hold `" where"`
  -- (103). No break placement joins this one, which is what the header measure has to cover for.
  ensureContains text "GenerousLongNames.Inner\n    where\n  solo := 0"
      "the default joined a `where` onto a return type that fills its own row"
  for line in text.splitOn "\n" do
    ensure (line.length <= 100) s!"the default put a row over the margin: {line}"
  let nextLine : LeanFmt.Internal.FormatConfig := { declarationWhere := .nextLine }
  let broken ←
    analyzeExact root application setup fixture.toString "Wheres.lean"
        s!"4j{(Lean.toJson nextLine).compress}"
  let (_, brokenText) ← canonical broken "declaration-where next-line"
  ensureContains brokenText "def documented (input : Nat) : Packet\n    where"
      "next-line kept `where` on a signature row that had room"
  ensureContains brokenText "def singleField (input : Nat) : Single\n    where"
      "next-line kept `where` on a short signature's row"

/-- `empty-structure-instance`: an instance with nothing in it is `{}` by default and `{ }` under
`spaced`, and the four ways a field-free instance is not empty are untouched by either.

`Term.structInst` spells its delimiters as the atoms `"{ "` and `" }"`, so the padding survives an
empty field list and the adapter copies it -- which is why the default has to *remove* something
rather than leave the document alone. Both spellings parse, so this is a preference; the fixture is
here rather than in `Families.lean` because the two values must render the same source.

The `with` clause, the `..` ellipsis, the type ascription, and an interior comment each leave the
field list empty while giving the braces something to hold. All four are asserted under the default,
because the collector's whole condition is one question asked of the source between the delimiters
and a wrong answer would delete a token rather than a space. -/
private def testEmptyStructureInstance (root work setup : System.FilePath) (application : String) :
    IO Unit := do
  let fixture := work / "EmptyInstances.lean"
  writeFile fixture
      "module\n\nstructure Pair where\n  a : Nat := 0\n  b : Nat := 0\n\ndef compactSource : Pair := \
        {}\n\ndef spacedSource : Pair := { }\n\ndef withClause (p : Pair) : Pair := \
        { p with a := 1 }\n\ndef ellipsis : Pair := { .. }\n\ndef ascribed : Pair := \
        ({ a := 0, b := 0 } : Pair)\n\ndef commented : Pair := { /- kept -/ }\n\ndef filled : Pair \
        := { a := 1 }\n"
  let compact : LeanFmt.Internal.FormatConfig := {}
  let report ←
    analyzeExact root application setup fixture.toString "EmptyInstances.lean"
        s!"4j{(Lean.toJson compact).compress}"
  let (_, text) ← canonical report "empty-structure-instance default"
  for spelled in ["def compactSource : Pair :=\n  {}", "def spacedSource : Pair :=\n  {}"] do
    ensureContains text spelled "the default did not write an empty instance as `{}`"
  for untouched in ["{ p with a := 1 }", "{ .. }", "{ a := 0, b := 0 }", "{ a := 1 }"] do
    ensureContains text untouched
        s!"the default rewrote a structure instance that is not empty: {untouched}"
  ensureContains text "/- kept -/" "the default dropped an interior comment"
  let spaced : LeanFmt.Internal.FormatConfig := { emptyStructureInstance := .spaced }
  let spacedReport ←
    analyzeExact root application setup fixture.toString "EmptyInstances.lean"
        s!"4j{(Lean.toJson spaced).compress}"
  let (_, spacedText) ← canonical spacedReport "empty-structure-instance spaced"
  for spelled in ["def compactSource : Pair :=\n  { }", "def spacedSource : Pair :=\n  { }"] do
    ensureContains spacedText spelled "`spaced` did not keep Lean's own `{ }`"
  ensure (text != spacedText) "the two values rendered the same bytes"

/-- `blank-lines-between-fields`, `-constructors`, and `-alternatives`, all five values over one
fixture holding each family: structure fields, inductive constructors, a pattern-matching
definition's alternatives, and `cases` alternatives.

The fixture writes one blank line in each of the first three lists, above an item that carries a
comment, so `never` has something to remove and `preserve` something to keep. It also has an item of
each kind the `around-*` values react to: a doc-commented field and constructor, a field and an
alternative with an own-row comment, and a field and an alternative too long for one row, which only
the render can tell. `around-multiline` reads that render, so its blank line next to the wrapped
items is the case a pass over the source alone could not produce. -/
private def testBlankLinesBetween (root work setup : System.FilePath) (application : String) :
    IO Unit := do
  let fixture := work / "Spacing.lean"
  let arrows := String.intercalate " → " (List.replicate 16 "Nat")
  let square := String.intercalate " + " (List.replicate 12 "s * s")
  writeFile fixture <|
      String.intercalate "\n"
        ["module", "", "structure Config where", "  name : String", "  path : String", "",
          "  /-- The number of retries. -/", "  retries : Nat", "  verbose : Bool",
          s!"  callback : {arrows}", "  -- The last field.", "  last : Nat", "",
          "inductive Shape where", "  | point", "  | line", "", "  /-- A circle. -/",
          "  | circle (radius : Nat)", "  | square (side : Nat)", "", "def area : Shape → Nat",
          "  | .point => 0", "  | .line => 0", "", "  -- Circles are approximated.",
          "  | .circle r => 3 * r * r", s!"  | .square s => {square}", "",
          "theorem zeroAdd (n : Nat) : 0 + n = n := by", "  cases n with", "  | zero => rfl",
          "  | succ m => simp", ""]
  let render (label : String) (spacing : LeanFmt.Internal.ElementSpacing) : IO String := do
    let format : LeanFmt.Internal.FormatConfig :=
      { blankLinesBetweenFields := spacing, blankLinesBetweenConstructors := spacing
        blankLinesBetweenAlternatives := spacing }
    let report ←
      analyzeExact root application setup fixture.toString "Spacing.lean"
          s!"4j{(Lean.toJson format).compress}"
    let (_, text) ← canonical report s!"blank-lines-between {label}"
    return text
  let never ← render "never" .never
  for expected in
    ["  path : String\n  /-- The number of retries. -/", "  | line\n  /-- A circle. -/",
      "  | .line => 0\n  -- Circles are approximated.", "  | zero => rfl\n  | succ m => simp"] do
    ensureContains never expected "`never` left a blank line between two items"
  let preserve ← render "preserve" .preserve
  for expected in
    ["  path : String\n\n  /-- The number", "  | line\n\n  /-- A circle.",
      "  | .line => 0\n\n  -- Circles", "  retries : Nat\n  verbose : Bool\n  callback :",
      "  | circle (radius : Nat)\n  | square"] do
    ensureContains preserve expected "`preserve` did not keep exactly the source's blank lines"
  let always ← render "always" .always
  for expected in
    ["  name : String\n\n  path : String\n\n  /--", "  | point\n\n  | line",
      "  | .point => 0\n\n  | .line => 0", "  | zero => rfl\n\n  | succ m => simp"] do
    ensureContains always expected "`always` left two items without a blank line"
  let annotated ← render "around-annotated" .aroundAnnotated
  for expected in
    ["  retries : Nat\n\n  verbose : Bool\n  callback :", "Nat\n\n  -- The last field.\n  last",
      "  | point\n  | line\n\n  /-- A circle.", "  | circle (radius : Nat)\n\n  | square",
      "  | .point => 0\n  | .line => 0", "  | .circle r => 3 * r * r\n\n  | .square s =>"] do
    ensureContains annotated expected "`around-annotated` misplaced a blank line"
  let multiline ← render "around-multiline" .aroundMultiline
  for expected in
    ["  retries : Nat\n\n  verbose : Bool\n\n  callback :\n", "Nat\n\n  -- The last field.\n  last",
      "  | point\n  | line", "  | circle (radius : Nat)\n\n  | square",
      "  | .circle r => 3 * r * r\n\n  | .square s =>\n", "  | zero => rfl\n  | succ m => simp"] do
    ensureContains multiline expected "`around-multiline` misplaced a blank line"

/-- `blank-lines-between-do-elements = "grouped"` and `compact-block-size`, against `preserve` and
the default `never`.

`grouped` separates two neighbouring elements when either spans several rows or their kinds differ,
and each kind rule has a pair in the fixture that would come out differently under a nearby rule:
`left.set` and `right.set` are one kind although their receivers differ, `discard <| …` and
`discard (…)` are one kind although one is spelled with an operator, and the reassignment
`total := 1` is not a `let`. The `for` body pairs a reassignment with a call, two kinds, so it is
the block `compact-block-size` keeps tight at 3 and leaves to `grouped` at 0. The blank line the
source writes after the first `let` is the one `never` removes and every other value keeps. -/
private def testBlankLinesBetweenDoElements (root work setup : System.FilePath)
    (application : String) : IO Unit := do
  let fixture := work / "DoSpacing.lean"
  writeFile fixture <|
      String.intercalate "\n"
        ["module", "", "def check (value : Bool) (label : String) : IO Unit :=",
          "  unless value do", "    throw <| IO.userError label", "",
          "def run (items : Array Nat) : IO Nat := do", "  let mut total := 0", "",
          "  let cell ← IO.mkRef 0", "  let left ← IO.mkRef 0", "  let right ← IO.mkRef 0",
          "  total := 1", "  for item in items do", "    total := total + item",
          "    cell.set total", "  left.set 1", "  right.set 2", "  discard <| cell.get",
          "  discard (cell.get)", "  check (total > 0) \"positive\"",
          "  check (total < 1000) \"bounded\"", "  -- Report it.",
          "  IO.println s!\"total {total}\"", "  return total", ""]
  let render (label : String) (spacing : LeanFmt.Internal.ElementSpacing) (compact : Nat) :
    IO String := do
    let format : LeanFmt.Internal.FormatConfig :=
      { blankLinesBetweenDoElements := spacing, compactBlockSize := compact }
    let report ←
      analyzeExact root application setup fixture.toString "DoSpacing.lean"
          s!"4j{(Lean.toJson format).compress}"
    let (_, text) ← canonical report s!"blank-lines-between-do-elements {label}"
    return text
  let never ← render "never" .never 0
  ensureContains never "  let mut total := 0\n  let cell ←"
      "`never` kept the source's blank line in a `do` block"
  let preserve ← render "preserve" .preserve 0
  for expected in
    ["  let mut total := 0\n\n  let cell ←", "  let right ← IO.mkRef 0\n  total := 1",
      "  right.set 2\n  discard <| cell.get"] do
    ensureContains preserve expected "`preserve` did not keep exactly the source's blank lines"
  let grouped ← render "grouped" .grouped 3
  for expected in
    ["  let mut total := 0\n\n  let cell ← IO.mkRef 0\n  let left ←",
      "  let right ← IO.mkRef 0\n\n  total := 1\n\n  for item in items do",
      "    total := total + item\n    cell.set total\n\n  left.set 1\n  right.set 2\n\n",
      "  discard <| cell.get\n  discard (cell.get)\n\n  check (total > 0)",
      "  check (total > 0) \"positive\"\n  check (total < 1000) \"bounded\"\n\n  -- Report it.\n",
      "  IO.println s!\"total {total}\"\n\n  return total"] do
    ensureContains grouped expected "`grouped` misplaced a blank line"
  let spread ← render "grouped, every block spaced" .grouped 0
  ensureContains spread "    total := total + item\n\n    cell.set total"
      "`compact-block-size = 0` still kept a short block tight"

/-- `blank-lines-between-tactics`, against `preserve` and the default `never`, in an indented block
and a bracketed one. The two-row `·` is the multiline tactic, so `around-multiline` sets it apart;
the source's blank line above it is the one `never` removes, and the one inside the braces shows a
bracketed block's tactics are a list too. At `compact-block-size = 5` the five-tactic block is
short enough to add nothing. -/
private def testBlankLinesBetweenTactics (root work setup : System.FilePath)
    (application : String) : IO Unit := do
  let fixture := work / "TacticSpacing.lean"
  writeFile fixture <|
      String.intercalate "\n"
        ["module", "", "theorem pair (a b : Nat) (h : a = b) : b = a ∧ a = a := by",
          "  have hb : b = b := rfl", "  have ha : a = a := rfl", "  constructor", "",
          "  · subst h", "    rfl", "  · exact ha", "", "example : True := by", "  {", "    skip",
          "", "    trivial }", ""]
  let render (label : String) (spacing : LeanFmt.Internal.ElementSpacing) (compact : Nat) :
    IO String := do
    let format : LeanFmt.Internal.FormatConfig :=
      { blankLinesBetweenTactics := spacing, compactBlockSize := compact }
    let report ←
      analyzeExact root application setup fixture.toString "TacticSpacing.lean"
          s!"4j{(Lean.toJson format).compress}"
    let (_, text) ← canonical report s!"blank-lines-between-tactics {label}"
    return text
  let never ← render "never" .never 0
  for expected in ["  constructor\n  · subst h", "  skip\n  trivial"] do
    ensureContains never expected "`never` kept the source's blank line between tactics"
  let preserve ← render "preserve" .preserve 0
  for expected in
    ["  constructor\n\n  · subst h", "    rfl\n  · exact ha", "  skip\n\n  trivial"] do
    ensureContains preserve expected "`preserve` did not keep exactly the source's blank lines"
  let multiline ← render "around-multiline" .aroundMultiline 0
  for expected in
    ["  have ha : a = a := rfl\n  constructor\n\n  · subst h\n    rfl\n\n  · exact ha",
      "  skip\n\n  trivial"] do
    ensureContains multiline expected "`around-multiline` misplaced a blank line between tactics"
  let compact ← render "around-multiline, compact" .aroundMultiline 5
  ensureContains compact "    rfl\n  · exact ha"
      "`compact-block-size = 5` still spaced a five-tactic block"

/-- `reflow-comments`: a standalone `--` block whose rows overflow the margin is repacked to fit
when the flag is on, and keeps its bytes when it is off. Empty comment lines split a block into
paragraphs packed independently; list items, pinned directives, trailing comments, and doc
comments keep their bytes either way. -/
private def testCommentReflow (root work setup : System.FilePath) (application : String) :
    IO Unit := do
  let fixture := work / "Reflow.lean"
  let long1 :=
    "-- This is a deliberately long comment line whose total width exceeds one hundred columns at its indentation, so the reflow must repack it."
  let long2 :=
    "-- A second paragraph, also long enough that it must be rewrapped on its own, independently of the first paragraph's packing."
  let bullet :=
    "-- - a bullet item that is quite long but must stay verbatim because reflow never moves list items"
  let pinned :=
    "-- shake: keep this pinned directive stays exactly where it is no matter how long its line runs"
  let doc :=
    "/-- A doc comment whose bytes are syntax and must stay exact however long the line runs on. -/"
  writeFile fixture
      ("module\n\n" ++ doc ++
        "\ntheorem documented : 1 + 1 = 2 := rfl\n\nexample : 1 + 1 = 2 := by\n  " ++
        long1 ++
        "\n  --\n  " ++
        long2 ++
        "\n  " ++
        bullet ++
        "\n  " ++
        pinned ++
        "\n  have h : 1 + 1 = 2 := rfl -- trailing bytes stay\n  exact h\n")
  let ensureFits (width : Nat) (text : String) : IO Unit := do
    for line in text.splitOn "\n" do
      ensure (line.length <= width) s!"a row over the margin survived reflow: {line}"
  let default : LeanFmt.Internal.FormatConfig := {}
  let off ←
    analyzeExact root application setup fixture.toString "Reflow.lean"
        s!"4j{(Lean.toJson default).compress}"
  let (_, offText) ← canonical off "reflow-comments default"
  ensureContains offText long1 "the default rewrapped a comment line"
  let reflow : LeanFmt.Internal.FormatConfig := { reflowComments := true }
  let on ←
    analyzeExact root application setup fixture.toString "Reflow.lean"
        s!"4j{(Lean.toJson reflow).compress}"
  let (_, onText) ← canonical on "reflow-comments on"
  ensureFits 100 onText
  ensureContains onText "--\n  -- A second paragraph" "the paragraph break did not survive"
  ensureContains onText "-- indentation, so the reflow must repack it."
      "the first paragraph's words did not survive"
  ensureContains onText "-- first paragraph's packing."
      "the second paragraph was packed against the first"
  ensureContains onText bullet "a list item lost its bytes"
  ensureContains onText pinned "a pinned directive lost its bytes"
  ensureContains onText "-- trailing bytes stay" "a trailing comment lost its bytes"
  ensureContains onText doc "a doc comment lost its bytes"
  -- The Hales-Jewett shape: a comment that fits at its source column overflows once canonical
  -- layout indents its block deeper, and must be repacked to the deeper row's smaller budget.
  let deep := work / "ReflowDeep.lean"
  writeFile deep
      "module\n\nexample (P : Nat → Prop) (h : ∀ n, P n) : P 1 := by\n  exact (by\n        -- This comment fits at column two but overflows once the enclosing construct gets indented\n        -- deeper by canonical layout, so it must be repacked to the deeper row's much smaller budget here.\n        exact h 1)\n"
  let deepReport ←
    analyzeExact root application setup deep.toString "ReflowDeep.lean"
        s!"4j{(Lean.toJson reflow).compress}"
  let (_, deepText) ← canonical deepReport "reflow-comments deep"
  ensureFits 100 deepText
  ensureContains deepText "-- here." "the deep block's last word did not land on its own row"

end DeclarationFormatter

public def main (args : List String) : IO UInt32 := do
  let root ← repoRoot
  let application := (root / ".lake" / "build" / "bin" / "lean-fmt").toString
  withScratchDir "declaration-formatter" fun work => do
      let setup ← setupFile root work "tests/fixtures/declaration-formatter/Families.lean"
      let cases : Array Case :=
        #[{ name := "width-20", run := DeclarationFormatter.testWidth root setup application 20 },
          { name := "width-40", run := DeclarationFormatter.testWidth root setup application 40 },
          { name := "width-80", run := DeclarationFormatter.testWidth root setup application 80 },
          { name := "width-100", run := DeclarationFormatter.testWidth root setup application 100 },
          { name := "narrow-layout",
            run := DeclarationFormatter.testNarrowLayout root setup application },
          { name := "wide-layout",
            run := DeclarationFormatter.testWideLayout root setup application },
          { name := "comments", run := DeclarationFormatter.testComments root setup application },
          { name := "declaration-body",
            run := DeclarationFormatter.testDeclarationBody root work setup application },
          { name := "declaration-where",
            run := DeclarationFormatter.testDeclarationWhere root work setup application },
          { name := "empty-structure-instance",
            run := DeclarationFormatter.testEmptyStructureInstance root work setup application },
          { name := "blank-lines-between",
            run := DeclarationFormatter.testBlankLinesBetween root work setup application },
          { name := "blank-lines-between-do-elements",
            run :=
              DeclarationFormatter.testBlankLinesBetweenDoElements root work setup application },
          { name := "blank-lines-between-tactics",
            run := DeclarationFormatter.testBlankLinesBetweenTactics root work setup application },
          { name := "comment-reflow",
            run := DeclarationFormatter.testCommentReflow root work setup application }]
      runCases "declaration-formatter" cases args
