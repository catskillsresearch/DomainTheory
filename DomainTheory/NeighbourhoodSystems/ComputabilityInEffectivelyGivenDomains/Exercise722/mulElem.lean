/-ai
The product of two elements of the domain collects those members of Scott's family that contain the concatenation of some neighbourhood of the first with some neighbourhood of the second. The set of all words is such a member, witnessed by the two master neighbourhoods. The intersection of two such members is again a member: the intersections of the witnessing neighbourhoods still belong to the two elements, monotonicity of concatenation puts their concatenation inside the intersection, and that concatenation is nonempty, so the intersection lies in the family. A larger member of the family containing such a concatenation is again a member.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **Scott's multiplication on `|S|`.** `xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`. The filter
conditions:

* `master_mem`: take `X = Y = Σ` (both in any filter), `Σ·Σ ⊆ Σ`;
* `inter_mem`: from witnesses `X₁Y₁ ⊆ Z₁`, `X₂Y₂ ⊆ Z₂`, the pair `X₁ ∩ X₂ ∈ x`, `Y₁ ∩ Y₂ ∈ y` (filter
  closure) gives `(X₁ ∩ X₂)(Y₁ ∩ Y₂) ⊆ Z₁ ∩ Z₂` by monotonicity of `concat`, and `Z₁ ∩ Z₂ ∈ S`
  because this non-empty witness sits inside it (positivity);
* `up_mem`: transitivity of `⊆`. -/
def mulElem (x y : Ssys.Element) : Ssys.Element where
  mem Z := InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z
  sub h := h.1
  master_mem :=
    ⟨InS.univ, Set.univ, x.master_mem, Set.univ, y.master_mem, Set.subset_univ _⟩
  inter_mem := by
    rintro Z1 Z2 ⟨hZ1, X1, hX1, Y1, hY1, hsub1⟩ ⟨hZ2, X2, hX2, Y2, hY2, hsub2⟩
    have hXi : x.mem (X1 ∩ X2) := x.inter_mem hX1 hX2
    have hYi : y.mem (Y1 ∩ Y2) := y.inter_mem hY1 hY2
    have hcsub : concat (X1 ∩ X2) (Y1 ∩ Y2) ⊆ Z1 ∩ Z2 := by
      intro w hw
      exact ⟨hsub1 (concat_mono Set.inter_subset_left Set.inter_subset_left hw),
             hsub2 (concat_mono Set.inter_subset_right Set.inter_subset_right hw)⟩
    have hne : (Z1 ∩ Z2).Nonempty :=
      (concat_nonempty (x.sub hXi).nonempty (y.sub hYi).nonempty).mono hcsub
    exact ⟨InS.inter hZ1 hZ2 hne, X1 ∩ X2, hXi, Y1 ∩ Y2, hYi, hcsub⟩
  up_mem := by
    rintro Z W ⟨_, X, hX, Y, hY, hsub⟩ hW hZW
    exact ⟨hW, X, hX, Y, hY, hsub.trans hZW⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
