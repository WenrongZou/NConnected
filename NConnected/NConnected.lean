-- Project 2: n-connected spaces
-- Author: Shuhan Wang, Wenrong Zou
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open scoped Topology

--#check HomotopyGroup.Pi
--#check (π_ 1)

--#check FundamentalGroup
--#check SimplyConnectedSpace


--#check HomotopyGroup.pi0EquivZerothHomotopy
--#check HomotopyGroup.pi1EquivFundamentalGroup



-- Definitions of n-connected maps and n-connected spaces


/-- A n-connected space: a topological space with trivial `π_i` for all `i ≤ n`. -/
@[mk_iff NConnected_def]
class NConnectedSpace (n : ℕ) (X : Type*) [TopologicalSpace X] : Prop where
  nconnected : ∀ x : X, ∀ i : ℕ, i ≤ n → Subsingleton (π_ i X x)


#check NConnectedSpace


-- 0-connected = path-connected
#check PathConnectedSpace
#check ZerothHomotopy
#check HomotopyGroup.pi0EquivZerothHomotopy


theorem zero_connected_iff_path_connected (X : Type*) [TopologicalSpace X] :
  NConnectedSpace 0 X ↔ PathConnectedSpace X := by
  constructor
  . rw [NConnected_def 0 X]
    intro h
    rw [pathConnectedSpace_iff_zerothHomotopy]
    have h0 : ∀ (x: X), Subsingleton (π_ 0 X x) := by
      intro x
      exact h x 0 (Nat.zero_le 0)
    have hzero: Subsingleton (ZerothHomotopy X) := by
      --rw [← HomotopyGroup.pi0EquivZerothHomotopy]
      --exact h0 (Classical.arbitrary X)
      sorry
    sorry
  . sorry
