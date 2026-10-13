module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.Syntax

/-!
# Named-variable notation for λ-terms

`Tm n` uses de Bruijn indices, which are hard to read: `λa b. a` is
`.lam (.lam (.var 1))`.  This file provides a term elaborator that lets λ-terms be written
with named variables, as in the paper, and a matching delaborator, so that concrete terms
are also *displayed* with names (in goals, hovers and `#check`).

* `[tm| λ a b. a]` is the closed term `.lam (.lam (.var 1)) : Tm 0`.
* `[tm| x y ⊢ y x]` is the open term `.app (.var 0) (.var 1) : Tm 2`: the names before `⊢`
  are the free variables in scope, the **last** one being de Bruijn index `0`
  (as in a context `Γ, x, y`).
* `⟪e⟫` inserts an arbitrary Lean term `e : Tm k`, where `k` is the number of variables in
  scope at that point, e.g. `[tm| x ⊢ ⟪Tm.K.embed⟫ x x]`.

Application associates to the left, and the body of a `λ` extends as far to the right as
possible: `[tm| λ f x. f (f x)]` is `λf. λx. (f (f x))`.

The elaborator produces exactly the de Bruijn term, so a definition written with the
notation is definitionally (indeed syntactically, up to numerals) the same as one written
with the constructors.
-/

public section

namespace NRT

open Lean Elab Term Meta

/-- Syntax of λ-terms with named variables. -/
declare_syntax_cat lam_tm

/-- A variable. -/
syntax ident : lam_tm
/-- Parentheses. -/
syntax "(" lam_tm ")" : lam_tm
/-- An arbitrary Lean term of type `Tm k`, `k` the number of variables in scope. -/
syntax "⟪" term "⟫" : lam_tm
/-- Abstraction over one or more variables, `λ x y. M`. -/
syntax:max "λ " ident+ ". " lam_tm : lam_tm
/-- Application, left associative. -/
syntax:60 lam_tm:60 ppSpace lam_tm:61 : lam_tm

/-- Elaborate named-variable syntax to a de Bruijn term.  `ctx` lists the variables in
scope, innermost (de Bruijn index `0`) first. -/
meta partial def elabLamTm (ctx : List Name) (stx : TSyntax `lam_tm) : TermElabM Expr := do
  let n := ctx.length
  match stx with
  | `(lam_tm| $x:ident) =>
    match ctx.idxOf? x.getId with
    | some i =>
      let fin ← elabTerm (← `(($(quote i) : Fin $(quote n)))) (some (mkApp (mkConst ``Fin) (toExpr n)))
      return mkApp2 (mkConst ``Tm.var) (toExpr n) fin
    | none => throwErrorAt x "unbound variable '{x.getId}' in λ-term"
  | `(lam_tm| ($t)) => elabLamTm ctx t
  | `(lam_tm| ⟪$e⟫) =>
    let e ← elabTermEnsuringType e (some (mkApp (mkConst ``Tm) (toExpr n)))
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | `(lam_tm| λ $xs*. $body) =>
    let names := xs.toList.map (·.getId)
    let ctx' := names.foldl (fun c x => x :: c) ctx
    let mut e ← elabLamTm ctx' body
    for k in (List.range names.length).reverse do
      e := mkApp2 (mkConst ``Tm.lam) (toExpr (n + k)) e
    return e
  | `(lam_tm| $f $a) =>
    return mkApp3 (mkConst ``Tm.app) (toExpr n) (← elabLamTm ctx f) (← elabLamTm ctx a)
  | _ => throwUnsupportedSyntax

/-- A closed λ-term with named variables, e.g. `[tm| λ a b. a] : Tm 0`. -/
elab:max "[tm| " t:lam_tm "]" : term => elabLamTm [] t

/-- An open λ-term with named free variables, e.g. `[tm| x y ⊢ y x] : Tm 2`; the last
name before `⊢` is the de Bruijn index `0`. -/
elab:max "[tm| " xs:ident* " ⊢ " t:lam_tm "]" : term =>
  elabLamTm (xs.toList.map (·.getId)).reverse t

/-! ## Delaborator

Concrete terms built from the constructors (with numeral indices) are displayed back in
`[tm| …]` form.  The variable bound at absolute depth `k` (counting from the outermost
binder, free variables first) is named by the `k`-th letter `a, b, c, …`. -/

open PrettyPrinter Delaborator SubExpr

/-- The display name of the variable at absolute depth `k`. -/
meta def lamTmName (k : ℕ) : Name :=
  if k < 26 then Name.mkSimple (String.singleton (Char.ofNat ('a'.toNat + k)))
  else Name.mkSimple s!"x{k}"

/-- Read a numeral `i : Fin m` or `i : ℕ`. -/
meta def lamTmNumeral? (e : Expr) : MetaM (Option ℕ) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => evalNat n
  | _ => evalNat e

/-- Convert a concrete term with `d` variables in scope back to named syntax. -/
meta partial def lamTmToSyntax (d : ℕ) (e : Expr) : MetaM (Option (TSyntax `lam_tm)) := do
  match e.getAppFnArgs with
  | (``Tm.var, #[_, i]) =>
    let some i ← lamTmNumeral? i | return none
    if i < d then return some (← `(lam_tm| $(mkIdent (lamTmName (d - 1 - i))):ident))
    else return none
  | (``Tm.app, #[_, f, a]) =>
    let some f ← lamTmToSyntax d f | return none
    let some a ← lamTmToSyntax d a | return none
    let f ← match f with
      | `(lam_tm| λ $_*. $_) => `(lam_tm| ($f))
      | _ => pure f
    let a ← match a with
      | `(lam_tm| $_:ident) => pure a
      | `(lam_tm| ($_)) => pure a
      | _ => `(lam_tm| ($a))
    return some (← `(lam_tm| $f $a))
  | (``Tm.lam, #[_, b]) =>
    let some b ← lamTmToSyntax (d + 1) b | return none
    let x := mkIdent (lamTmName d)
    match b with
    | `(lam_tm| λ $ys*. $body) => return some (← `(lam_tm| λ $x $ys*. $body))
    | _ => return some (← `(lam_tm| λ $x:ident. $b))
  | _ => return none

/-- Display concrete abstractions and applications in `[tm| …]` form. -/
@[delab app.NRT.Tm.lam, delab app.NRT.Tm.app]
meta def delabLamTm : Delab := do
  let e ← getExpr
  let some n ← lamTmNumeral? e.getAppArgs[0]! | failure
  let some s ← lamTmToSyntax n e | failure
  if n = 0 then `([tm| $s])
  else
    let xs := (List.range n).toArray.map fun k => mkIdent (lamTmName k)
    `([tm| $xs* ⊢ $s])

/-! ## Examples -/

example : [tm| λ a b. a] = .lam (.lam (.var 1)) := rfl
example : [tm| λ f x. f x x] = .lam (.lam (.app (.app (.var 1) (.var 0)) (.var 0))) := rfl
example : [tm| x y ⊢ y x] = (.app (.var 0) (.var 1) : Tm 2) := rfl
example : [tm| λ h a k. k (h (λ x. x)) (h (λ x. a x x))] =
    .lam (.lam (.lam (.app (.app (.var 0) (.app (.var 2) (.lam (.var 0))))
      (.app (.var 2) (.lam (.app (.app (.var 2) (.var 0)) (.var 0))))))) := rfl
example (t : Tm 1) : [tm| x ⊢ λ y. ⟪rename Fin.succ t⟫ y] =
    .lam (.app (rename Fin.succ t) (.var 0)) := rfl

end NRT
