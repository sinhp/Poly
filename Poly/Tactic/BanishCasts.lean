import Mathlib.Tactic.Basic

/-! Try to remove cast-like terms from the goal
by turning their equality argument into `refl`.

Supported cast-like terms:
- `cast`
- `Eq.rec`
- `Eq.mpr`
- `Eq.mp`
- `CategoryTheory.eqToHom`
- `CategoryTheory.eqToIso`

1. Identify all cast-like terms.
2. For each equality there, identify the differences using `congr`-like operation.
2a. For each difference, try to _prove_ it.
    Very often a proof term for the difference will already appear in the goal somewhere:
    use a generalized `assumption` tactic that finds such terms.
3. `generalize_proofs`
4. For each difference, generalize the RHS or LHS.
   If RHS appears in LHS, generalize LHS; if vice-verse, generalize RHS;
   otherwise generalize LHS.
5. Case on the difference with generalized LHS. -/

-- assumption' : like assumption but can find proof terms in the goal type
-- or one of the target types

open Lean Meta Elab Term in
/-- If `h : a = b` (`h : HEq a b`) proves an equality (resp. heterogeneous equality),
`eq_lhs% h` is the left-hand-side `a`. -/
elab "eq_lhs%" h:term : term => do
  let A ← mkFreshTypeMVar
  let l ← mkFreshExprMVar A
  let r ← mkFreshExprMVar A
  let _ ← elabTerm h (← mkAppOptM ``Eq #[A, l, r])
  -- TODO HEq
  instantiateMVars l

open Lean Meta Elab Term in
/-- If `h : a = b` (`h : HEq a b`) proves an equality (resp. heterogeneous equality),
`eq_rhs% h` is the right-hand-side `b`. -/
elab "eq_rhs%" t:term : term => do
  let A ← mkFreshTypeMVar
  let l ← mkFreshExprMVar A
  let r ← mkFreshExprMVar A
  let _ ← elabTerm t (← mkAppOptM ``Eq #[A, l, r])
  -- TODO HEq
  instantiateMVars r
