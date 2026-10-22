module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **Every finite (principal) element is computable** (Scott's remark after 7.2: "If `y` were
finite, the set of indices would be recursive"). For the finite element `↑Xₙ`, the index set
`{m ∣ Xₙ ⊆ Xₘ}` is a recursive slice of `incl_computable` (fix the first index to `n` by the
primitive-recursive reindex `m ↦ ⟨n, m⟩`), hence r.e. -/
theorem principal_isComputableElement (P : ComputablePresentation V) (n : ℕ) :
    ComputableElement P (V.principal (P.mem_X n)) := by
  have hg : Nat.Primrec (fun m => Nat.pair n m) :=
    ((Nat.Primrec.const n).pair primrec_id).of_eq (fun _ => rfl)
  have hrec : RecDecidable (fun m => P.X n ⊆ P.X m) :=
    RecDecidable.of_iff (fun m => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P.incl_computable.comp hg)
  constructor
  refine (RecDecidable.of_iff (fun m => ?_) hrec).re
  simp only [mem_principal]
  exact ⟨fun h => h.2, fun h => ⟨P.mem_X m, h⟩⟩

end DomainTheory.NeighbourhoodSystems
