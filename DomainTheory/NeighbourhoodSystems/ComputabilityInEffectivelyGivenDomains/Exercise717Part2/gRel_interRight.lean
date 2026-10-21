/-ai
The catamorphism is closed under intersection of the target.

The argument inducts on the first relation. At the master, inversion forces the second target to be the master as well, so the intersection is the master. At a zero embedding, inversion recovers a relation of the leaf map, and the intersection law of that map supplies the leaf clause. At a paired embedding, inversion of the second relation supplies a second pair of intermediate neighbourhoods. The inductive hypotheses intersect them, and the monotonicity and intersection laws of the node map, applied to the product of the intersections, supply the node clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_cod
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_gamma_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embZero_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embPair_inv

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Intersectivity on the output (Scott's 2.1(ii)). -/
theorem gRel_interRight (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {Z'}, GRel u v W Z' → GRel u v W (Z ∩ Z') := by
  induction h with
  | @gamma Z hZ =>
      intro Z' h'
      subst hZ
      have hZ' := gRel_gamma_inv hD h'
      subst hZ'
      rw [Set.inter_self]
      exact GRel.gamma rfl
  | @leaf X Z hrel =>
      intro Z' h'
      exact GRel.leaf (u.inter_right hrel (gRel_embZero_inv hD h'))
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro Z' h'
      obtain ⟨Z₁', Z₂', hP', hQ', hv'⟩ := gRel_embPair_inv hD h'
      have hgP : GRel u v P (Z₁ ∩ Z₁') := ihP hP'
      have hgQ : GRel u v Q (Z₂ ∩ Z₂') := ihQ hQ'
      refine GRel.node hgP hgQ ?_
      have hmem : (prod E E).mem (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) :=
        prod_mem_prodNbhd (gRel_cod hgP) (gRel_cod hgQ)
      have hv1 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z :=
        v.mono hvrel (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_left, Set.inter_subset_left⟩)
          subset_rfl hmem (v.rel_cod hvrel)
      have hv2 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z' :=
        v.mono hv' (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩)
          subset_rfl hmem (v.rel_cod hv')
      exact v.inter_right hv1 hv2

end Exercise717

end DomainTheory.NeighbourhoodSystems
