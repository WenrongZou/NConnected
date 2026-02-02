import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected

/- In this file, define [n-connected space](https://ncatlab.org/nlab/show/n-connected+space).
A topological space `X` is `n`-cconected space iff its homotopy group is trivial up to degree `n`.
-/

variable (X : Type*) [TopologicalSpace X]

/-- A topological space `X` is `n`-connected space iff its homotopy group is trivial up
to degree `n`. -/
class NConnected (n : ℕ) : Prop where
  nonempty : Nonempty X
  trivial_homotopy (x : X) {k : ℕ} (hk : k ≤ n) : Subsingleton (HomotopyGroup.Pi k X x)
/- drop nonempty-/

namespace NConnected

/- the topological space is 0-connected iff it is connected. -/
theorem nConnected_zero_iff_pathConnectedSpace :
    NConnected X 0 ↔ PathConnectedSpace X := by
  have iff_aux : NConnected X 0 ↔
    Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
    constructor
    · intro ⟨h₁, h₂⟩
      let x := Classical.choice h₁
      let equiv_aux : (HomotopyGroup.Pi 0 X x) ≃ ZerothHomotopy X :=
        HomotopyGroup.pi0EquivZerothHomotopy
      haveI : Subsingleton (HomotopyGroup.Pi 0 X x) := (h₂ x (Nat.zero_le 0))
      exact ⟨Equiv.nonempty equiv_aux.symm, Equiv.subsingleton.symm equiv_aux⟩
    · intro ⟨h, h'⟩
      let x := Classical.choice ((nonempty_quotient_iff _).mp h)
      exact ⟨(nonempty_quotient_iff _).mp h, fun _ _ hk => Nat.eq_zero_of_le_zero hk ▸
        Equiv.subsingleton HomotopyGroup.pi0EquivZerothHomotopy⟩
  rw [pathConnectedSpace_iff_zerothHomotopy]
  exact iff_aux

lemma of_le {n m : ℕ} (h : m ≤ n) : NConnected X n → NConnected X m :=
  fun h' => ⟨h'.1, fun x _ hk => h'.2 x (.trans hk h)⟩

/-- one connected is equivalent to simply connected. -/
theorem nConnected_one_iff_simplyConnectedSpace :
    NConnected X 1 ↔ SimplyConnectedSpace X := by
  constructor
  · intro h
    haveI : NConnected X 0 := of_le X zero_le_one h
    rw [simply_connected_iff_paths_homotopic]
    constructor
    · exact (nConnected_zero_iff_pathConnectedSpace X).mp this
    · intro x y
      haveI := (h.trivial_homotopy x (le_refl 1))
      refine {allEq := ?_}
      intro p q
      by_contra hc
      obtain eq_aux₀ := (Equiv.subsingleton.symm HomotopyGroup.pi1EquivFundamentalGroup).allEq
        (p.trans p.symm) (q.trans p.symm)
      have : p = q :=
        calc
          _ = (p.trans p.symm).trans p := by simp
          _ = q := by simp [(Equiv.subsingleton.symm HomotopyGroup.pi1EquivFundamentalGroup).allEq
        (p.trans p.symm) (q.trans p.symm)]
      exact hc this
  · intro h
    obtain ⟨path_connected_X, h'⟩ := simply_connected_iff_paths_homotopic.mp h
    constructor
    · exact path_connected_X.nonempty
    · intro x k hk
      by_cases hk₀ : k = 0
      · rw [hk₀]
        rw [pathConnectedSpace_iff_zerothHomotopy] at path_connected_X
        obtain ⟨h₁, h₂⟩ := path_connected_X
        exact Equiv.subsingleton HomotopyGroup.pi0EquivZerothHomotopy
      · have hk₁ : k = 1 := by omega
        rw [hk₁]
        haveI : Subsingleton (FundamentalGroup X x) := h' x x
        exact Equiv.subsingleton (HomotopyGroup.pi1EquivFundamentalGroup)
