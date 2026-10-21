/-ai
For every neighbourhood of the infinite iterate and every bound N, some list of length N reproduces, under the enumeration, the first N fibers of that neighbourhood.

The proof is by induction on N. The empty list covers length zero. At a successor the inductive list is extended by an index of the next fiber, which exists because the enumeration is surjective. A position before the old length still reads the old list, and the last position reads the appended index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- Build, by induction on `N`, a list of fiber indices reproducing `W`'s first `N` fibers. -/
theorem exists_list_fiber {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    ∀ N, ∃ L : List ℕ, L.length = N ∧ ∀ j, j < N → P.X (L.getD j P.masterIdx) = fiber W j := by
  intro N
  induction N with
  | zero => exact ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    obtain ⟨L, hlen, hL⟩ := ih
    obtain ⟨n, hn⟩ := P.surj (hW.1 N)
    refine ⟨L ++ [n], by simp [List.length_append, hlen], fun j hj => ?_⟩
    by_cases h : j < N
    · rw [getD_append_cf L [n] P.masterIdx (by rw [hlen]; exact h)]
      exact hL j h
    · have hjN : j = N := by omega
      subst hjN
      rw [getD_append_right_cf L [n] P.masterIdx hlen.le, hlen, Nat.sub_self,
        List.getD_cons_zero]
      exact hn

end Iterate

end DomainTheory.NeighbourhoodSystems
