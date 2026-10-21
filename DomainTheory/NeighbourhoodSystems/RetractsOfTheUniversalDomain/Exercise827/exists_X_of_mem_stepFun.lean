/-ai
If the closed form of the product of d at the approximable map of x lies in the step function of a list of rational pairs, then some neighbourhood X lies in x, is contained in that step function, and is self-related by the product.

Proceed by induction on the list. The empty list is witnessed by the master neighbourhood of the function space: it lies in x, simplification puts it inside the empty step function, and the master relation is a self-relation. For a cons cell, membership splits into the head step and the tail step function. The single-step theorem and the inductive hypothesis supply two neighbourhoods. Their intersection lies in x. It is contained in the step function of the cons cell because the two inclusions pass inside the intersection. Each self-relation pushes to the intersection by monotonicity, using that membership in x makes each piece and the intersection neighbourhoods of the function space, and the intersection law on the right combines the two relations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.exists_X_of_mem_step

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.27(b)(3)(b), assembled over a whole `stepFun` list.** Induction on the list `L`
using `exists_X_of_mem_step` for the head pair and the inductive hypothesis for the tail, combined
via `x.inter_mem` (giving the ambient validity of the intersection "for free", `x.sub`) and
`(piD d).mono`/`.inter_right` (self-relation of an intersection of two self-related nbhds). -/
theorem exists_X_of_mem_stepFun (d : ApproximableMap U U) (x : (funSpace U U).Element)
    (L : List (Set ℚ × Set ℚ)) (hmem : piDApply d (toApproxMap x) ∈ stepFun L) :
    ∃ X, x.mem X ∧ X ⊆ (stepFun L : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  induction L with
  | nil =>
    refine ⟨(funSpace U U).master, x.master_mem, ?_, (piD d).master_rel⟩
    simp
  | cons p L ih =>
    rw [stepFun_cons] at hmem
    obtain ⟨hmemP, hmemL⟩ := hmem
    obtain ⟨Xp, hXpx, hXpsub, hXpXp⟩ := exists_X_of_mem_step d x hmemP
    obtain ⟨XL, hXLx, hXLsub, hXLXL⟩ := ih hmemL
    refine ⟨Xp ∩ XL, x.inter_mem hXpx hXLx, ?_, ?_⟩
    · rw [stepFun_cons]
      exact Set.inter_subset_inter hXpsub hXLsub
    · have hvalidP : (funSpace U U).mem Xp := x.sub hXpx
      have hvalidL : (funSpace U U).mem XL := x.sub hXLx
      have hvalidInter : (funSpace U U).mem (Xp ∩ XL) := x.sub (x.inter_mem hXpx hXLx)
      have h1 : (piD d).rel (Xp ∩ XL) Xp :=
        (piD d).mono hXpXp Set.inter_subset_left subset_rfl hvalidInter hvalidP
      have h2 : (piD d).rel (Xp ∩ XL) XL :=
        (piD d).mono hXLXL Set.inter_subset_right subset_rfl hvalidInter hvalidL
      exact (piD d).inter_right h1 h2

end DomainTheory.NeighbourhoodSystems
