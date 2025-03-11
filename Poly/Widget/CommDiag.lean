/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel
import Mathlib.CategoryTheory.Category.Basic

/-! ## Definitions copied from Mathlib.Tactic.Widget.CommDiag

We don't want to import it because it registers an `ExprPresenter`
that is worse than the one here. -/

open Lean in
/-- If the expression is a function application of `fName` with 7 arguments, return those arguments.
Otherwise return `none`. -/
@[inline] def Lean.Expr.app7? (e : Expr) (fName : Name) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 7 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.appArg!
    )
  else
    none

namespace Mathlib.Tactic.Widget
open Lean
open CategoryTheory

/-- Given a Hom type `α ⟶ β`, return `(α, β)`. Otherwise `none`. -/
def homType? (e : Expr) : Option (Expr × Expr) := do
  let some (_, _, A, B) := e.app4? ``Quiver.Hom | none
  return (A, B)

/-- Given composed homs `g ≫ h`, return `(g, h)`. Otherwise `none`. -/
def homComp? (f : Expr) : Option (Expr × Expr) := do
  let some (_, _, _, _, _, f, g) := f.app7? ``CategoryStruct.comp | none
  return (f, g)

end Mathlib.Tactic.Widget

/-! ## Metaprogramming utilities for breaking down category theory expressions -/

namespace Mathlib.Tactic.Widget
open Lean Meta
open ProofWidgets
open CategoryTheory

/-- Given a composite hom `f ≫ g ≫ … ≫ h` (parenthesized in any way),
return `(dom f, [(f, cod f), (g, cod g), …, (h, cod h)])`. -/
partial def splitHomComps (f : Expr) : MetaM (Expr × List (Expr × Expr)) := do
  let fTp ← inferType f >>= instantiateMVars
  let some (X, _) := homType? fTp | throwError "expected morphism, got {f}"
  return (X, ← go f)
where go (f : Expr) : MetaM (List (Expr × Expr)) := do
  if let some (f, g) := homComp? f then
    return (← go f) ++ (← go g)
  else
    let fTp ← inferType f >>= instantiateMVars
    let some (_, Y) := homType? fTp | throwError "expected morphism, got {f}"
    return [(f, Y)]

structure DiagState where
  /-- vertex id ↦ object -/
  vertices: Std.HashMap Nat Expr := .empty
  /-- morphism `f` ↦ (src, tgt) for every occurrence of `f` -/
  edges: Std.HashMap Expr (List (Nat × Nat)) := .empty
  freshVertId : Nat := 0

variable {m : Type → Type} [Monad m] [MonadStateOf DiagState m]

/-- Add a hom `f : X ⟶ Y`.
If `f` already exists in the diagram,
the first edge matching `f` is reused.
Otherwise a new free-floating edge (with new endpoints) is created.
Returns the source and target vertices. -/
def addHom (f X Y : Expr) : m (Nat × Nat) := do
  let es := (← get).edges.getD f []
  if let some (s, t) := es.head? then
    return (s, t)
  modifyGet fun { vertices, edges, freshVertId } =>
    let src := freshVertId
    let tgt := freshVertId + 1
    ((src, tgt), {
      vertices := vertices.insert src X |>.insert tgt Y
      edges := edges.insert f ((src, tgt) :: es)
      freshVertId := freshVertId + 2
    })

/-- Add a hom `f : _ ⟶ Y`, ensuring that it starts at vertex `src`.
If an edge for `f` starting at `src` already exists in the diagram,
that edge is reused.
Otherwise a new edge with a new target is created.
Returns the target vertex. -/
def addHomFrom (f Y : Expr) (src : Nat) : m Nat := do
  let es := (← get).edges.getD f []
  for (s, t) in es do
    if s == src then
      return t
  modifyGet fun { vertices, edges, freshVertId } =>
    let tgt := freshVertId
    (tgt, {
      vertices := vertices.insert tgt Y
      edges := edges.insert f ((src, tgt) :: es)
      freshVertId := freshVertId + 1
    })

/-- Add a hom `f`, ensuring its endpoints are `src` and `tgt`.
If an edge for `f` with these endpoints already exists in the diagram,
that edge is reused.
Otherwise a new edge is created. -/
-- TODO: the current approach means that f ≫ g = f ≫ h merges f
-- but g ≫ f = h ≫ f does not merge f. It should be symmetric instead!
def addHomFromTo (f : Expr) (src tgt : Nat) : m Unit := do
  let es := (← get).edges.getD f []
  for (s, t) in es do
    if s == src && t == tgt then
      return
  modify fun st => { st with edges := st.edges.insert f ((src, tgt) :: es) }

def addEq [MonadLift MetaM m] (eq : Expr) : m Unit := do
  let some (_, lhs, rhs) := eq.eq? | (throwError "no diagram" : MetaM Unit)
  let (X, ((l, Y) :: ls)) ← splitHomComps lhs | (throwError "no diagram" : MetaM Unit)
  let (_, ((r, Z) :: rs)) ← splitHomComps rhs | (throwError "no diagram" : MetaM Unit)
  let mut (src, tgt) ← addHom l X Y
  for (l, Y) in ls do
    tgt ← addHomFrom l Y tgt
  let lTgt := tgt
  tgt ← addHomFrom r Z src
  for h : i in [:rs.length-1] do
    let (r, Z) := rs[i]'(by have := h.upper; dsimp +zetaDelta at this; omega)
    tgt ← addHomFrom r Z tgt
  if !rs.isEmpty then
    let (r, _) := rs[rs.length - 1]!
    addHomFromTo r tgt lTgt

open Jsx in
def mkLabel (e : Expr) : MetaM (Nat × Nat × Html) := do
  let fmt ← withOptions (·.setNat `pp.deepTerms.threshold 1)
    (toString <$> ppExpr e)
  let w := min (15 + fmt.length * 6) 100
  let h := max 20 (20 * (1 + fmt.length / 15))
  let x: Int := -w/2
  let y: Int := -h/2
  return (w, h, <g>
    <rect
      fill="var(--vscode-editor-background)"
      stroke="var(--vscode-editor-foreground)"
      strokeWidth={.num 1.5}
      width={w} height={h} x={x} y={y}
      rx={5}
    />
    <foreignObject width={w} height={h} x={.num (x + 5 : Int)} y={y}>
      <span className="font-code">{.text fmt}</span>
    </foreignObject>
  </g>)

open Jsx in
def toHtml [MonadLift MetaM m] : m Html := do
  let st ← get
  let mut maxLabelRadius := 0.0
  let mut vertices := #[]
  for (vId, v) in st.vertices do
    let (w, h, label) ← mkLabel v
    maxLabelRadius := max maxLabelRadius (Float.sqrt <| (w.toFloat/2)^2 + (h.toFloat/2)^2)
    vertices := vertices.push {
      id := toString vId
      boundingShape := .rect w.toFloat h.toFloat
      label
    }
  let mut edges := #[]
  for (f, l) in st.edges do
    let (w, h, label) ← mkLabel f
    maxLabelRadius := max maxLabelRadius (Float.sqrt <| (w.toFloat/2)^2 + (h.toFloat/2)^2)
    for (s, t) in l do
      edges := edges.push {
        source := toString s
        target := toString t
        attrs := #[("className", "dim")]
        label? := some label
        details? := some
          <span>
            <InteractiveCode fmt={← Widget.ppExprTagged f} />
            :
            <InteractiveCode fmt={← Widget.ppExprTagged (← inferType f)}/>
            <br/>
          </span>
      }
  return <GraphDisplay
    vertices={vertices}
    edges={edges}
    forces={#[
      .link { distance? := some (maxLabelRadius * 4) },
      .manyBody { strength? := some (-150) },
      .x { strength? := some 0.01 },
      .y { strength? := some 0.01 }
    ]}
    showDetails={true}
  />

open Jsx in
@[expr_presenter]
def commutativeDiagramPresenter : ExprPresenter where
  userName := "Commutative diagram"
  layoutKind := .block
  present type := do
    let type ← instantiateMVars type
    let x : StateT DiagState MetaM Html := do
      addEq type
      toHtml
    x.run' {}

-- Show the widget in downstream modules.
show_panel_widgets [GoalTypePanel]
