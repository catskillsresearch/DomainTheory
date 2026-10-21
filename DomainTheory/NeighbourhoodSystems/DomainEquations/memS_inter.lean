/-ai
If X, Y, and Z are neighbourhoods of D-sharp and Z is contained in the intersection of X and Y, then that intersection is a neighbourhood of D-sharp.

The argument inducts on the construction of X. When X is the master, Y is contained in X, so the intersection is Y. When X is a zero-copy of A and Y is the master, the intersection is that zero-copy. If Y is a zero-copy of B, the witness Z must itself be a zero-copy of some C contained in the intersection of A and B, and the intersection law of D supplies that intersection; a master or pair witness for Z contradicts the shape of a zero-embedding. If Y is a pair, the intersection with the zero-copy is empty, contradicting that Z is nonempty. When X is a pair, the cases of Y the master and of Y a zero-copy are symmetric. If Y is another pair, the witness Z is a pair whose sides lie under the two component intersections, and the inductive hypotheses close those intersections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 — closure under consistent intersection.** Scott's central verification, "by
induction on the number of steps required to put `X` and `Y` into `𝒟^§`". The cross cases
(`0A ∩ (1P∪2Q) = ∅`, etc.) are discharged because the consistency witness `Z` is non-empty
(`memS_nonempty`); the `0A ∩ 0B` case uses `𝒟`'s own closure; the `(1P∪2Q) ∩ (1P'∪2Q')` case recurses
on `P, P'` and `Q, Q'`. -/
theorem memS_inter {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ {X : Set (List Bool × α)}, MemS D X → ∀ {Y : Set (List Bool × α)}, MemS D Y →
      ∀ {Z : Set (List Bool × α)}, MemS D Z → Z ⊆ X ∩ Y → MemS D (X ∩ Y) := by
  intro X hX
  induction hX with
  | gamma =>
    intro Y hY Z _ _
    rw [Set.inter_eq_right.mpr (memS_subset_gamma hY)]; exact hY
  | @zero A hA =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hA)]; exact MemS.zero hA
    | @zero B hB =>
      rw [embZero_inter]
      -- the witness `Z` must be a `0C`; read off `C ⊆ A ∩ B`, then `D`'s closure gives `A ∩ B ∈ 𝒟`.
      rw [embZero_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        exact MemS.zero (D.inter_mem hA hB hC (embZero_subset.mp hsub))
      | @pair P Q hP hQ =>
        obtain ⟨t, hmem⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hempty : t.1 = [] := (hsub hmem).1
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · rw [hp'] at hempty; exact absurd hempty (by simp)
        · rw [hq'] at hempty; exact absurd hempty (by simp)
    | @pair P Q _ _ =>
      rw [embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
  | @pair P Q hP hQ ihP ihQ =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))]
      exact MemS.pair hP hQ
    | @zero B hB =>
      rw [Set.inter_comm, embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
    | @pair P' Q' hP' hQ' =>
      rw [embPair_inter]
      rw [embPair_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        obtain ⟨a, ha⟩ := hD C hC
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ embZero C from ⟨rfl, ha⟩)) (by simp)
      | @pair Z₀ Z₁ hZ₀ hZ₁ =>
        obtain ⟨hsub₀, hsub₁⟩ := embPair_subset.mp hsub
        exact MemS.pair (ihP hP' hZ₀ hsub₀) (ihQ hQ' hZ₁ hsub₁)

end Example61

end DomainTheory.NeighbourhoodSystems
