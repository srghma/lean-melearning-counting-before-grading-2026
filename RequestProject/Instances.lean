module

public import Mathlib
public import RequestProject.ResourceLogic

/-!
# Three instances of the 1995 framework (Section 5), and the idempotence dial

* **Binding-time logic** `BT = {D, S}` (`D = 0`, `S = 1`), `+` = join, `·` = meet; the
  grade at an application is `(i + k) j` and the combination table is checked.
* **Trust logic** `Trust = {U, T}` (`U = 0`, `T = 1`); the grade at an application is
  `j k` (meet), and the trust coercion `·; Γ ⊢ Δ; · ⟹ ·; Γ ⊢ T + Δ; ·` is derived from `(+k)_R`.
* **Logic of unity** `Unity = {0, 1, ω}` with `ω` (the `≤ ∞` grade) reusable, and
  permeability `P_L^→(A) = A^ω`, `P_R^→(A^ω) = A` (and symmetrically).
* **Idempotence dial**: the qualitative algebras satisfy `k · k = k`; `ℕ` does not, and
  `1 + 1 = 2` there.
-/

@[expose] public section

namespace RML

/-! ## Binding-time algebra -/

/-- Binding times: `D` (dynamic, `= 0`) and `S` (static, `= 1`). -/
inductive BT : Type
  | D | S
  deriving DecidableEq, Fintype

namespace BT

/-- `+` is join. -/
def add : BT → BT → BT
  | S, _ => S
  | D, k => k

/-- `·` is meet. -/
def mul : BT → BT → BT
  | D, _ => D
  | S, k => k

instance : Add BT := ⟨add⟩
instance : Mul BT := ⟨mul⟩
instance : Zero BT := ⟨D⟩
instance : One BT := ⟨S⟩

instance : CommSemiring BT where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

@[simp] theorem zero_def : (0 : BT) = D := rfl
@[simp] theorem one_def : (1 : BT) = S := rfl

end BT

/-- **Binding-time combination table** (Section 5): the redex grade `(i + k) j` for all
eight combinations, exactly as tabulated in the paper. -/
theorem bt_table :
    [(BT.D, BT.D, BT.D, BT.D), (.D, .D, .S, .D), (.D, .S, .D, .D), (.D, .S, .S, .S),
     (.S, .D, .D, .D), (.S, .D, .S, .D), (.S, .S, .D, .S), (.S, .S, .S, .S)].all
      (fun r => decide ((r.1 + r.2.2.1) * r.2.1 = r.2.2.2)) = true := by
  decide

/-- A redex is static iff the function is static and at least one of `i`, `k` is. -/
theorem bt_static_iff (i j k : BT) : (i + k) * j = .S ↔ j = .S ∧ (i = .S ∨ k = .S) := by
  revert i j k; decide

/-! ## Trust algebra -/

/-- Trust levels: `U` (untrusted, `= 0`) and `T` (trusted, `= 1`). -/
inductive Trust : Type
  | U | T
  deriving DecidableEq, Fintype

namespace Trust

/-- `+` is join. -/
def add : Trust → Trust → Trust
  | T, _ => T
  | U, k => k

/-- `·` is meet. -/
def mul : Trust → Trust → Trust
  | U, _ => U
  | T, k => k

instance : Add Trust := ⟨add⟩
instance : Mul Trust := ⟨mul⟩
instance : Zero Trust := ⟨U⟩
instance : One Trust := ⟨T⟩

instance : CommSemiring Trust where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

@[simp] theorem zero_def : (0 : Trust) = U := rfl
@[simp] theorem one_def : (1 : Trust) = T := rfl

end Trust

/-- **Trust combination.** The grade `j k` of an application is trusted iff both the
function and the argument are trusted. -/
theorem trust_app_iff (j k : Trust) : j * k = .T ↔ j = .T ∧ k = .T := by
  revert j k; decide

/-- **Trust coercion** (derived from `(+k)_R` with `k = T`): from `·; Γ ⊢ Δ; ·` derive
`·; Γ ⊢ T + Δ; ·`, i.e. every conclusion may be coerced to trusted. Holds for any choice of
permeability operators and with or without the scaling rule. -/
theorem trust_coerce {P : Permeability Trust} {sc : Bool} {Γ Δ : List (Fm Trust × Trust)}
    (h : Deriv P sc [] Γ Δ []) :
    Deriv P sc [] Γ (Δ.map fun e => (e.1, Trust.T + e.2)) [] := by
  refine coerce h (List.forall₂_same.2 fun e _ => ⟨rfl, ⟨0, (add_zero _).symm⟩⟩) ?_
  clear h
  induction Δ with
  | nil => exact .nil
  | cons e Δ ih =>
    refine .cons ⟨rfl, Trust.T, ?_⟩ ih
    show Trust.T + e.2 = e.2 + Trust.T
    exact add_comm _ _

/-! ## The logic of unity -/

/-- Grades of the logic of unity: `zero`, `one`, and the reusable "of course" grade
`omega` (`≤ ∞`). -/
inductive Unity : Type
  | zero | one | omega
  deriving DecidableEq, Fintype

namespace Unity

/-- Addition: `0` is neutral, otherwise the result is `ω` (in particular `1 + 1 = ω`). -/
def add : Unity → Unity → Unity
  | zero, k => k
  | k, zero => k
  | _, _ => omega

/-- Multiplication: `0` absorbs, `1` is neutral, `ω · ω = ω`. -/
def mul : Unity → Unity → Unity
  | zero, _ => zero
  | _, zero => zero
  | one, k => k
  | k, one => k
  | omega, omega => omega

instance : Add Unity := ⟨add⟩
instance : Mul Unity := ⟨mul⟩
instance : Zero Unity := ⟨zero⟩
instance : One Unity := ⟨one⟩

instance : CommSemiring Unity where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

@[simp] theorem zero_def : (0 : Unity) = zero := rfl
@[simp] theorem one_def : (1 : Unity) = one := rfl

end Unity

/-- Permeability of the logic of unity: `P_L^→(A) = P_L^←(A) = A^ω`,
`P_R^←(A) = A^ω` and `P_R^→(A^ω) = A` (defined only on grade `ω`). -/
def unityPerm : Permeability Unity where
  pLr A e := e = (A, .omega)
  pLl A e := e = (A, .omega)
  pRl A e := e = (A, .omega)
  pRr e A := e = (A, .omega)

/-- Dereliction in the logic of unity: `·; A^ω ⊢ ·; A`. -/
theorem unity_dereliction {sc : Bool} (A : Fm Unity) :
    Deriv unityPerm sc [] [(A, .omega)] [] [A] :=
  Deriv.pLr (Ψ := []) rfl (Deriv.id₂ A)

/-- `·; A^ω ⊢ A^ω; ·` in the logic of unity. -/
theorem unity_id_omega {sc : Bool} (A : Fm Unity) :
    Deriv unityPerm sc [] [(A, .omega)] [(A, .omega)] [] :=
  Deriv.pRl (Δ := []) rfl (unity_dereliction A)

/-- The grade `ω` is reusable: an `ω`-assumption may be contracted (`ω + ω = ω`). -/
theorem unity_contract {P : Permeability Unity} {sc : Bool} {Ψ Θ} {Γ Δ} {A : Fm Unity}
    (h : Deriv P sc Ψ ((A, .omega) :: (A, .omega) :: Γ) Δ Θ) :
    Deriv P sc Ψ ((A, .omega) :: Γ) Δ Θ :=
  Deriv.cL h

/-- …and it may be weakened (weakening at grade `0`, then coercion `0 + ω = ω`). -/
theorem unity_weaken {P : Permeability Unity} {sc : Bool} {Γ Δ} {A : Fm Unity}
    (h : Deriv P sc [] Γ Δ []) : Deriv P sc [] ((A, .omega) :: Γ) Δ [] :=
  Deriv.addL (i := 0) Unity.omega (Deriv.wL A h)

/-! ## The idempotence dial -/

/-- The qualitative instances are multiplicatively idempotent. -/
theorem bt_mul_idem (k : BT) : k * k = k := by revert k; decide

theorem trust_mul_idem (k : Trust) : k * k = k := by revert k; decide

/-- `ℕ`, the quantitative instance, is not multiplicatively idempotent… -/
theorem nat_not_mul_idem : ¬ ∀ k : ℕ, k * k = k := fun h => by
  have := h 2; omega

/-- …and it genuinely counts: `1 + 1 = 2 ≠ 1`, whereas in `BT` and `Trust`, `1 + 1 = 1`. -/
theorem nat_counts : (1 : ℕ) + 1 = 2 ∧ (1 : ℕ) + 1 ≠ 1 := by decide

theorem bt_one_add_one : (1 : BT) + 1 = 1 := by decide

theorem trust_one_add_one : (1 : Trust) + 1 = 1 := by decide

/-! ## The usage instance `ℕ` -/

/-- In the usage logic over `ℕ`, the scaling rule `(·k)` is admissible for every `k ≥ 1`
in the system without `(·k)`, via additive coercion `k i = i + (k - 1) i`. -/
theorem nat_scale_admissible {P : Permeability ℕ} {k : ℕ} (hk : 1 ≤ k)
    {Γ Δ : List (Fm ℕ × ℕ)} (h : Deriv P false [] Γ Δ []) :
    Deriv P false [] (scaleZone k Γ) (scaleZone k Δ) [] := by
  refine scale_admissible (fun i => ⟨(k - 1) * i, ?_⟩) h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end RML
