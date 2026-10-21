/-ai
The composite of two computable approximable maps is computable.

The two graphs are recursively enumerable. Reindex one so that a code presents the domain index against a middle index, and the other so that it presents that middle index against the codomain index; conjoin them and project away the middle index. The composite relates a domain neighbourhood to a codomain neighbourhood exactly when some middle neighbourhood witnesses both relations. Surjectivity of the middle presentation turns that neighbourhood into an index, using that a related neighbourhood lies in the middle system, and an index conversely supplies the enumerated middle neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.Basic

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
    (hf : IsComputableMap P Q f) (hg : IsComputableMap Q R g) :
    IsComputableMap P R (g.comp f) := by
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf
  have hg' : REPred (fun s => g.rel (Q.X s.unpair.1) (R.X s.unpair.2)) := hg
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
