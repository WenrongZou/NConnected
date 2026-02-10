-- Project 2: n-connected spaces, n-connected maps.
-- Author: Shuhan Wang, Wenrong Zou

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Circle

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

/- Our next goal is to define `n`-connected map. To define this, we shall first
define `homotopy fibre`. -/

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homotopy fiber of `f` over `y`. -/
def hFiber (f : C(X, Y)) (y : Y) : Type (max u v) :=
  Σ x : X, Path (f x) y

-- We shall first endow homotopy fibre a topological structure:
instance (f : C(X, Y)) (y : Y) : TopologicalSpace (hFiber f y) := by
  unfold hFiber; infer_instance


/-- `f` is `n`-connected if all homotopy fibers are `(n-1)`-connected spaces. -/
def NConnectedMap (f : C(X, Y)) (n : ℕ) : Prop :=
  ∀ y : Y,
    match n with
    | 0     => Nonempty (hFiber f y)      -- 0-connected = nonempty fiber
    | n+1   => NConnected (hFiber f y) n  -- (n+1)-connected map → n-connected fiber

/- The definition of `f : X → Y` being a `n`-connected map is given by:
1. 0-connected if `π_0 f : π_0 (X) → π_0 (Y)` is surjective;
2. n-connected if `π_0 f : π_0 (X) → π_0 (Y)` is bijective and for any basepoint,
`π_i (f,x) : π_i (X,x) → π_i (Y,x)` are bijective for `1≤ i≤ n-1` and surjective for `i=n`.

  However, we don't have proper definition of `π_i f` in mathlib. Therefore, we adopted above
definition. Now we'd like to check compatibility of two definition. Due to lack of proper
definition of `π_i f`, we need to first define it (we only check `n=0` case, as for `n≥ 1`
case, it will involve LES of fibration.
-/


def ZerothHomotopy.map (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  Quotient.map (fun x : X => (f x)) fun _ _ ⟨p⟩ => ⟨p.map f.continuous⟩

/- Now we'd like to show that `f is 0-connected map` defined by us is equivalent to `π_0 f`
surjective. -/

theorem zeroConnected_surjective_ZH (f : C(X, Y))
  (h0 : NConnectedMap f 0) :
  Function.Surjective (ZerothHomotopy.map f) :=
by
   intro cy
   refine Quotient.inductionOn cy ?_
   intro y
   obtain ⟨x, p⟩ := h0 y
   refine ⟨Quotient.mk (pathSetoid X) x, ?_⟩
   exact Quotient.sound ⟨p⟩


theorem surjective_ZH_zeroConnected (f : C(X, Y))
  (hs : Function.Surjective (ZerothHomotopy.map f)) :
  NConnectedMap f 0 :=
by
  intro y
  rcases hs (Quotient.mk _ y) with ⟨cx, hcxy⟩
  refine Quotient.inductionOn cx ?_ hcxy
  intro x hxy
  have hj : Joined (f x) y := by
    have : (Quotient.mk _ (f x) : ZerothHomotopy Y) = Quotient.mk _ y := by
      simpa [ZerothHomotopy.map] using hxy
    exact Quotient.exact this
  rcases hj with ⟨p⟩
  exact ⟨⟨x, p⟩⟩

/-- `f` is 0-connected if and only if `π_0 f` is surjective -/
theorem zeroConnected_iff_surjective_ZH (f : C(X, Y)) :
  NConnectedMap f 0
    ↔ Function.Surjective (ZerothHomotopy.map f) :=
by
  constructor
  · intro h0; exact zeroConnected_surjective_ZH f h0
  · intro hs; exact surjective_ZH_zeroConnected f hs


namespace HomotopyGroup

open scoped unitInterval Topology
open scoped Topology.Homotopy

variable {X : Type*} [TopologicalSpace X] (x : X)





lemma genLoopEquivOfUnique_transAt (p q : Ω^ (Fin 1) X x) :
    genLoopEquivOfUnique (X := X) (x := x) (Fin 1)
        (GenLoop.transAt (N := Fin 1) (X := X) (x := x) (0 : Fin 1) q p)
      =
    (genLoopEquivOfUnique (X := X) (x := x) (Fin 1) q).trans
      (genLoopEquivOfUnique (X := X) (x := x) (Fin 1) p) := by
  ext t
  simp [GenLoop.transAt, genLoopEquivOfUnique, GenLoop.copy, Path.trans]
  have update_const_fin1 (t v : I) : Function.update (fun _ : Fin 1 => t) (0 : Fin 1) v
  = (fun _ : Fin 1 => v) := by
    ext j
    cases Unique.eq_default j
    simp [Function.update]
  simp [update_const_fin1]; rfl




/-- `pi1EquivFundamentalGroup` has group isomorphism structure. -/
def pi1MulEquivFundamentalGroup :
    (π_ 1 X x) ≃* FundamentalGroup X x :=
  { toEquiv := HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)
    map_mul' := by
     intro a b
     refine Quotient.inductionOn₂ a b ?_
     intro p q
     simp only [HomotopyGroup.mul_spec (N := Fin 1) (X := X) (x := x) (i := (0 : Fin 1))]
     apply Quotient.sound
     simp [genLoopEquivOfUnique_transAt]
     }

/-- `pi1EquivFundamentalGroup` is a group isomorphism. -/
theorem pi1EquivFundamentalGroup_isGroupIso :
    ∃ e : (π_ 1 X x) ≃* FundamentalGroup X x,
      e.toEquiv = HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x) :=
by
  refine ⟨pi1MulEquivFundamentalGroup (X := X) (x := x), rfl⟩

end HomotopyGroup
