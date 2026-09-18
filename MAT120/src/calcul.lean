import Verbose.French.ExampleLib
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# `on calcule avec` : a calculation tactic that accepts extra facts

**Author's note.** This file is both the implementation and its documentation.
It is written for colleagues who teach with Verbose Lean and who, like the
author of the course, have never written a line of Lean metaprogramming.
Everything needed to reproduce the construction is explained inline.

## 1. The problem this solves

Verbose Lean offers `par calcul` to justify a step by pure computation.  Under
the hood (see `Verbose/Tactics/Common.lean`, `computeAtGoalTac`) it runs
roughly

    iterate 3 (try first | done | rfl | simp_compute | gcongr_compute
                         | na_ring | norm_num | linarith only | na_abel)

The crucial detail is `linarith only`: the `only` means *without using any
hypothesis from the context*.  This is a deliberate pedagogical choice --
`par calcul` means "this is true by computation alone, no mathematical input
needed".  Consequently a step such as

    (x/y + y/x) * (x*y) ≤ 2 * (x*y)          -- from h : x/y + y/x ≤ 2 and k : x*y > 0

is out of reach of `par calcul`, because it genuinely uses two hypotheses.
The Verbose alternatives (`par lemma appliqué à ...`, `puisque ...`) then force
the student either to name a Mathlib lemma (`mul_le_mul_of_nonneg_right`) or to
drop into raw Mathlib tactics (`field_simp`, `nlinarith`) inside a `car` block.
Both break the illusion that the student is writing ordinary mathematics.

`on calcule avec h et k` fills exactly this gap: it is `par calcul`, plus the
facts you explicitly hand it.

## 2. What it looks like for the student

    Fait k : x*y > 0 car on calcule avec hx et hy

    Calc (x-y)^2 = (x/y+y/x-2)*(x*y) car on calcule avec hx et hy
       _ ≤ 0 car on calcule avec h et k

It accepts **either convention**, which matters a lot in practice:

  * by name:      `on calcule avec h et k`
  * by statement: `on calcule avec x > 0 et y > 0`

Verbose's own `puisque` accepts only the second form; giving it a hypothesis
name produces a confusing error, because `sinceTac` elaborates the term and
uses the resulting *proof* where a *statement* is expected.  Supporting both
removes a trap that costs beginners a lot of time.

## 3. Where it can be used

Inside a `Calc` block it is used through the existing `car` escape hatch:
`_ ≤ 0 car on calcule avec h et k`.  A genuine `par calcul avec h et k` step
would require forking Verbose: `convertCalcStepFR` in `Verbose/French/Calc.lean`
is an ordinary `def` that pattern-matches the alternatives of the `CalcStepFR`
syntax category one by one and ends with `throwUnsupportedSyntax`, with no
macro expansion.  Adding an alternative to the category is therefore not enough;
that function has to be edited.  Using `car` costs one French word and keeps
the library untouched.

## 4. Why *these* tactics, and not others

This is the question a colleague will ask first, so here is the honest answer,
in two parts.

### 4.1 How the list was actually obtained

**Empirically, not from a curriculum model.**  The list was grown from the
concrete steps that failed while formalising the exercise
`x ≠ y, x > 0, y > 0 ⊢ x/y + y/x > 2`: each tactic was added because some step
of that proof needed it, and the ordering is cheapest-first.  It was only
*afterwards* audited against chapters 1-2 of the course notes.  Anyone
reproducing this should expect to grow their own list the same way, from their
own exercises.

### 4.2 What each tactic corresponds to in the course

The audit is reassuring, because the course itself tells us what "calcul"
means.  Remarque 2.5 of the notes states the schema of a direct proof:

    hypothèse → définition → calcul → conclusion

and §2.12 ("Conseils de rédaction") asks the student to "justifier les étapes
qui ne sont pas immédiates" -- i.e. immediate computations are *not* to be
justified.  `on calcule avec` is the formal counterpart of that third arrow:
the steps the textbook performs silently.  Concretely:

| tactic                | property used | where it appears in chapters 1-2 |
|-----------------------|---------------|----------------------------------|
| `linarith [facts]`    | ordered-field axioms, restricted to *linear* combinations of the hypotheses with positive rational coefficients | Prop. 2.19 (from `x+3 = y+3` conclude `x = y`); Ex. 2.18 (`2n+2 > n`); the final inequality of the pigeonhole proof; any step combining two bounds |
| `nlinarith [facts]`   | compatibility of the order with *multiplication*: from `a ≤ b` and `0 ≤ c` infer `a*c ≤ b*c`; and `t^2 ≥ 0` | multiplying an inequality by a positive quantity, and every argument using a square as a nonnegative quantity |
| `positivity`          | sign of an expression built from `+`, `*`, `^`, `/` | `N > 1` in Euclid's proof (Thm. 2.12); the nonzero denominators of Def. 2.10; `x*y > 0` from `x > 0`, `y > 0` |
| `field_simp`          | field axiom `x * x⁻¹ = 1` for `x ≠ 0`, i.e. clearing denominators under a nonzero hypothesis | Def. 2.10 (`x = m/n`, `n ≠ 0`); Thm. 2.20 (`n(n+1)/2`); the ceiling `⌈N/n⌉` of §2.10 |
| `ring1`               | commutative ring identities | Prop. 2.4 (`(2k)^2 = 2(2k^2)`), Prop. 2.6, Prop. 2.7 (`(2k+1)^2 = 2(2k^2+2k)+1`), Prop. 2.16, the induction step of Thm. 2.20 |
| `field_simp; ring1` etc. | the two combined | statements mixing division with a ring identity: first clear denominators, then it is a ring problem |

So the answer to "benchmark-driven or curriculum-driven?" is: benchmark-driven
in origin, curriculum-compatible after checking.  The design principle that
emerges, and the one worth reusing, is *not* "mirror what a first-year student
knows", but:

> the tactic should absorb exactly those steps that the course itself performs
> without justification.

That distinction matters, because `linarith` and `nlinarith` are far stronger
than any student's manual toolkit (`linarith` is a complete decision procedure
for linear arithmetic over ordered fields).  The tactic is a *trusted
calculation oracle*, not a model of student knowledge.

### 4.3 Does it trivialise the exercises?

Checked, and no: `on calcule avec hxy, hx et hy` fails on the full statement
`x/y + y/x > 2`.  The student still has to find the mathematics (argue by
contradiction, introduce `(x-y)^2`); only the algebra is absorbed.  This is
worth re-checking whenever a tactic is added to the list.

## 5. Known limitations

* **Integers are not covered.**  Most of chapter 2 is about `ℤ`: parity,
  divisibility, `n = 2k`.  This battery is oriented towards ordered fields.
  The natural counterpart for `ℤ`/`ℕ` is `omega` (linear integer arithmetic,
  which knows about divisibility by a literal and about `%`), and `decide` for
  closed statements.  Adding `| (omega)` to the list is a one-line change.
* **No error explanation.**  On failure the student gets one French sentence
  plus the goal.  Verbose's own tactics can do better (they analyse the goal
  and suggest a phrasing); see `Verbose/French/Help.lean`.
* **`nlinarith` can be slow** when it fails, since it tries products of
  hypotheses.  It is placed after `linarith` for that reason.
* **At most four facts.**  `on calcule avec` reuses Verbose's own `factsFR`
  syntax category (the one behind `et`, `puisque`, `par ... appliqué à`), which
  is defined in `Verbose/French/Common.lean` with exactly four hard-coded
  variants (`term`, `term et term`, `term, term et term`,
  `term, term, term et term`) and no general "list of arbitrary length" rule.
  So `on calcule avec ha, hb, hc et hd` (four facts) works, but a fifth fact
  fails to parse ("unexpected token ','; expected 'et'") rather than being
  silently dropped.  This is a limitation of Verbose itself, not of the code
  below; extending it would mean editing `factsFR`, not just this file.  If a
  step needs more than four facts, combine some of them into an intermediate
  `Fait` first.

## 6. References for writing your own Verbose tactics

* Patrick Massot, *Teaching Mathematics Using Lean and Controlled Natural
  Language*, ITP 2024, DOI 10.4230/LIPIcs.ITP.2024.27 (a copy ships with the
  library, `.lake/packages/verbose/itp2024_paper.pdf`).  §4.1 covers the
  configuration a teacher can do **without** metaprogramming; §5 is the
  relevant one here -- it explains `elab`, syntax quotations and the
  `CoreM`/`MetaM`/`TacticM` monads, using the very same pattern we use below.
* `.lake/packages/verbose/CONTRIBUTING.MD` -- file organisation: `Tactics/`
  holds the language-independent implementation, `French/` and `English/` hold
  only the syntax and the messages.  A new tactic should follow that split.
* `.lake/packages/verbose/basic-configuration.md` -- the declarative
  customisation points (`configureAnonymousComputeLemmas`,
  `addAnonymousFactSplittingLemma`, ...).  **Try these first**: if all you need
  is to teach `par calcul` a few extra lemmas, no metaprogramming is required.
* The best models to copy are `Verbose/French/We.lean` (short `elab`
  declarations) and `Verbose/French/Claim.lean` (short `macro` declarations).
-/

section Tactique

/- Lean's metaprogramming API lives in these namespaces; opening them lets us
write `elabTerm` instead of `Lean.Elab.Term.elabTerm`, etc.  `Verbose.French`
is opened for `factsFR` (the "h et k" syntax category) and `factsFRToArray`. -/
open Lean Meta Elab Tactic Verbose.French

/-- Turn one "fact" into a term that denotes a **proof**.

A fact may be written in two ways, and we must tell them apart:

* `h`, the name of a hypothesis.  Elaborating it yields a proof, so there is
  nothing to do.
* `x > 0`, a statement.  Elaborating it yields a *proposition*, and we must
  still produce a proof of it.

`Meta.isProp e` answers "is `e` a proposition?" (as opposed to a proof of one).
In the second case we wrap the statement in `strongAssumption%`, a term
elaborator provided by Verbose (`Verbose/Tactics/Common.lean`) which proves a
statement from at most one local hypothesis -- the same search `puisque` uses.

`withoutModifyingState` is important: we elaborate only to *inspect* the term,
and we do not want the metavariables created on the way to leak into the real
proof state. -/
def faitVersPreuve (t : Term) : TacticM Term := do
  let estEnonce ← withoutModifyingState do
    let e ← elabTerm t none
    Meta.isProp e
  if estEnonce then `(strongAssumption% $t) else return t

/-- `on calcule avec h et k` : like `par calcul`, but additionally allowed to
use the given facts, together with the usual properties of the real numbers
(ordered ring, field, positivity).

A fact may be given by name (`h`) or by statement (`x > 0`). -/
syntax "on calcule avec " factsFR : tactic

/-- Capitalised variant, for use at the start of a proof line. -/
syntax "On calcule avec " factsFR : tactic

/- `elab_rules` attaches a meaning to a syntax declared above.  Read the
pattern `` `(tactic| on calcule avec $facts:factsFR) `` as: "when the user
writes this, bind the part matching `factsFR` to the variable `facts`".

`withMainContext` runs the body in the local context of the current goal, which
is what makes the hypotheses `h`, `k` visible to `elabTerm`.

`factsFRToArray` turns the French list `h et k` into `#[h, k]`; the syntax
category accepts up to four facts, written `a, b, c et d`.

The last step builds a tactic *syntactically* and runs it with `evalTactic`.
Inside the quotation, `$fs,*` splices our array as a comma-separated list, so
`linarith [$fs,*]` becomes `linarith [h, k]`.  `first | t₁ | t₂ | ...` tries
each alternative in turn and backtracks on failure, so the ordering below is
the real design decision (cheapest first, linear before nonlinear, and
denominators cleared only as a last resort).

Note `(field_simp; done)`: without `done`, a branch that simplifies the goal
without closing it would count as a success and stop the search, leaving the
goal open.  Each compound branch must therefore end in a closing tactic. -/
elab_rules : tactic
  | `(tactic| on calcule avec $facts:factsFR) => withMainContext do
    let fs ← (factsFRToArray facts).mapM faitVersPreuve
    evalTactic (← `(tactic|
      first
      | (linarith [$fs,*])
      | (nlinarith [$fs,*])
      | (positivity)
      | (field_simp; done)
      | (field_simp; ring1)
      | (field_simp; linarith [$fs,*])
      | (field_simp; nlinarith [$fs,*])
      | (fail "Ce calcul ne semble pas découler des faits fournis.")))

/- `macro_rules` is the lightweight cousin of `elab_rules`: instead of running
code, it rewrites one piece of syntax into another.  Here the capitalised form
simply expands to the lowercase one, so there is a single implementation. -/
macro_rules
  | `(tactic| On calcule avec $facts:factsFR) => `(tactic| on calcule avec $facts)

end Tactique

/-! ## Worked examples

These double as the test suite: if one of them breaks, the tactic changed.  -/

section Exemples

/-- Multiplying an inequality by a positive quantity (the step `par calcul`
cannot do).  Facts given by name. -/
example (x y : ℝ) (h : x/y + y/x ≤ 2) (k : x*y > 0) :
    (x/y+y/x)*(x*y) ≤ 2*(x*y) := by
  on calcule avec h et k

/-- The same, with the facts given by statement instead of by name. -/
example (x y : ℝ) (h : x/y + y/x ≤ 2) (k : x*y > 0) :
    (x/y+y/x)*(x*y) ≤ 2*(x*y) := by
  on calcule avec x/y + y/x ≤ 2 et x*y > 0

/-- An identity requiring the denominators to be cleared first. -/
example (x y : ℝ) (hx : x > 0) (hy : y > 0) :
    (x-y)^2 = (x/y+y/x-2)*(x*y) := by
  on calcule avec hx et hy

/-- Sign of a product. -/
example (x y : ℝ) (hx : x > 0) (hy : y > 0) : x*y > 0 := by
  on calcule avec hx et hy

/-- Combining two bounds (purely linear). -/
example (x y : ℝ) (h2 : x ≤ 4) (h : y ≤ 5) : x + y ≤ 4 + 5 := by
  on calcule avec h2 et h

/-- Inside a `Calc` block, through `car`. -/
example (x y : ℝ) (h1 : x + y ≥ 10) (h2 : x ≤ 4) (h : y ≤ 5) : (10:ℝ) ≤ 9 := by
  Calc (10:ℝ) ≤ x + y par h1
     _ ≤ 4 + 5 car on calcule avec h2 et h
     _ = 9 par calcul

/- Failure message, when the goal does not follow from the facts. -/
/--
error: Ce calcul ne semble pas découler des faits fournis.
x y : ℝ
h : x ≤ 4
⊢ x + y ≤ 4
-/
#guard_msgs in
example (x y : ℝ) (h : x ≤ 4) : x + y ≤ 4 := by
  on calcule avec h

/- The tactic does **not** prove the whole exercise on its own: the student
still has to supply the mathematical idea. -/
/--
error: Ce calcul ne semble pas découler des faits fournis.
x y : ℝ
hxy : x ≠ y
hx : x > 0
hy : y > 0
⊢ x / y + y / x > 2
-/
#guard_msgs in
example (x y : ℝ) (hxy : x ≠ y) (hx : x > 0) (hy : y > 0) : x/y + y/x > 2 := by
  on calcule avec hxy, hx et hy

end Exemples
