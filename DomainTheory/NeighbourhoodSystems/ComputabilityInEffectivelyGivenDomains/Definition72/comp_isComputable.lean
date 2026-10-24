module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.ComputableMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.ComputableElement

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **Proposition 7.3 (Scott 1981, PRG-19) — composition of computable maps is computable.** For
`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`, surjectivity of the middle presentation `Q` lets the witness `Y`
range over indices `l` (`Y = Yₗ`); the resulting `∃ l, Xₙ f Yₗ ∧ Yₗ g Zₖ` is recursively enumerable
by reindexing (`REPred.comp`), conjunction (`REPred.and`), and existential projection
(`REPred.proj`). -/
theorem comp_isComputable {U : NeighborhoodSystem γ}
    {P : ComputablePresentation V} {Q : ComputablePresentation W} {R : ComputablePresentation U}
    {f : ApproximableMap V W} {g : ApproximableMap W U}
    (hf : ComputableMap P Q f) (hg : ComputableMap Q R g) :
    ComputableMap P R (g.comp f) := by
  constructor
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf.out
  have hg' : REPred (fun s => g.rel (Q.X s.unpair.1) (R.X s.unpair.2)) := hg.out
  have hgf : Nat.Primrec (fun u => Nat.pair u.unpair.2.unpair.1 u.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hgg : Nat.Primrec (fun u => Nat.pair u.unpair.1 u.unpair.2.unpair.2) :=
    Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.right.comp Nat.Primrec.right)
  refine REPred.of_iff (fun t => ?_) ((hf'.comp hgf).and (hg'.comp hgg)).proj
  simp only [comp_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨Y, hfY, hgY⟩
    obtain ⟨l, rfl⟩ := Q.surj (g.rel_dom hgY)
    exact ⟨l, hfY, hgY⟩
  · rintro ⟨l, hfl, hgl⟩
    exact ⟨Q.X l, hfl, hgl⟩

end DomainTheory.NeighbourhoodSystems
