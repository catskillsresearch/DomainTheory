/-ai
Combining two found-pairs by a computable union is primitive recursive.

The two inputs and their found and value components are projections, and the union index of the two values is primitive recursive. Selection on the second found flag between the updated union and the first input, then selection on the first found flag between that result and the second input, equals the combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combineFound2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem primrec_combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) :
    Nat.Primrec (fun t : ℕ => combineFound2 hUnion t.unpair.1 t.unpair.2) := by
  have h0 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hf0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp h0
  have hf1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp h1
  have hv0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp h0
  have hv1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp h1
  have hunion : Nat.Primrec
      (fun t : ℕ => hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
    (hUnion.unionIdx_primrec.comp (hv0.pair hv1)).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun t : ℕ => selectFn t.unpair.2.unpair.1
      (Nat.pair 1 (hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2)) t.unpair.1) :=
    primrec_selectFn hf1 ((Nat.Primrec.const 1).pair hunion) h0
  exact (primrec_selectFn hf0 hinner h1).of_eq fun t => by unfold combineFound2; simp only []

end DomainTheory.NeighbourhoodSystems
