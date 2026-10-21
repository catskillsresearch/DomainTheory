/-ai
For each natural number n, projection from the infinite iterate onto the n-th coordinate is a computable map from the iterate presentation to the original presentation.

Inclusion of enumerated neighbourhoods is recursively decidable. Substituting the n-th coded list entry, defaulting to the master index, reduces the projection relation to that inclusion: the relation says that the n-th fiber is contained in the target, and the membership conjuncts hold because the enumerated set and the target are neighbourhoods. The resulting decidable predicate is recursively enumerable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510





section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)



variable {P}















theorem projN_isComputable (P : ComputablePresentation V) (n : ℕ) :
    IsComputableMap (iterPresentation P) P (projN V n) := by
  have hincl : RecDecidable (fun s => P.X s.unpair.1 ⊆ P.X s.unpair.2) := P.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (nthCode t.unpair.1 n P.masterIdx) t.unpair.2) :=
    ((primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.const n).pair (Nat.Primrec.const P.masterIdx)))).of_eq
        (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [iterPresentation_X, projN_rel, fiber_iterEnum, iterIdx, unpair_pair_fst,
    unpair_pair_snd]
  exact ⟨fun h => h.2.2, fun h => ⟨iterEnum_mem _, P.mem_X _, h⟩⟩

end Iterate
end DomainTheory.NeighbourhoodSystems
