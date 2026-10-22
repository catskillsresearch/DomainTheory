module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubDX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_subset_computable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section Computability

variable (P : ComputablePresentation D)

/-- **`SubDX n ∩ SubDX m = SubDX k` is recursively decidable.** Chain of exact rewrites reduces
membership-equality of a *pairwise* intersection to a *single* subset-decidable statement at the
`appendListCode`-combined index: `nbhdGen(decodeList n) ∩ nbhdGen(decodeList m) = nbhdGen(decodeList
k)` `↔` (`nbhdGen_inter`) `nbhdGen(decodeList n ++ decodeList m) = nbhdGen(decodeList k)` `↔`
(`appendListCode_eq`) `nbhdGen(decodeList(appendListCode n m)) = nbhdGen(decodeList k)` `↔`
(`nbhdGen_eq_iff`) `finGen(decodeList(appendListCode n m)) = finGen(decodeList k)` `↔`
(`Set.Subset.antisymm_iff`) both inclusions, each an instance of `finGen_subset_computable`
reindexed along the primitive-recursive `appendListCode`. -/
theorem SubD_interEq_computable :
    RecDecidable₃ (fun n m k => SubDX P n ∩ SubDX P m = SubDX P k) := by
  have hiff : ∀ n m k, SubDX P n ∩ SubDX P m = SubDX P k ↔
      finGen P (decodeList (appendListCode n m)) ⊆ finGen P (decodeList k) ∧
        finGen P (decodeList k) ⊆ finGen P (decodeList (appendListCode n m)) := by
    intro n m k
    show nbhdGen P (decodeList n) ∩ nbhdGen P (decodeList m) = nbhdGen P (decodeList k) ↔ _
    rw [nbhdGen_inter, ← appendListCode_eq, nbhdGen_eq_iff, Set.Subset.antisymm_iff]
  have hg1 : Nat.Primrec (fun t : ℕ => appendListCode t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_appendListCode.comp
        (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hreindex1 : Nat.Primrec (fun t : ℕ =>
      Nat.pair (appendListCode t.unpair.1 t.unpair.2.unpair.1) t.unpair.2.unpair.2) :=
    hg1.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hreindex2 : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.2 (appendListCode t.unpair.1 t.unpair.2.unpair.1)) :=
    (Nat.Primrec.right.comp Nat.Primrec.right).pair hg1
  have hforward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1)) ⊆
        finGen P (decodeList t.unpair.2.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbackward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList t.unpair.2.unpair.2) ⊆
        finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1))) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (hforward.and hbackward)
  exact hiff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

end Computability

end DomainTheory.NeighbourhoodSystems
