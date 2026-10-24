module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_2

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α β γ : Type*}
variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/- concordance: source L4305 PROPOSITION 7.3 computable maps form a category -/
/-- **Proposition 7.3 (consequence) (Scott 1981, PRG-19).** "If `f : 𝒟 → ℰ` is computable and
`x ∈ |𝒟|` is computable, then `f(x) ∈ |ℰ|` is also computable." Here `f(x) = {Yₘ ∣ ∃ Xₙ ∈ x, Xₙ f Yₘ}`
(`toElementMap`); surjectivity of `P` lets the witness `X` range over indices `n`, and the resulting
`∃ n, Xₙ ∈ x ∧ Xₙ f Yₘ` is r.e. by `REPred.and`/`REPred.proj`. -/
theorem apply_isComputableElement {P : ComputablePresentation V} {Q : ComputablePresentation W}
    {f : ApproximableMap V W} (hf : ComputableMap P Q f) {x : V.Element}
    (hx : ComputableElement P x) : ComputableElement Q (f.toElementMap x) := by
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf.out
  have hx' : REPred (fun n => x.mem (P.X n)) := hx.out
  constructor
  refine REPred.of_iff (fun m => ?_) ((hx'.comp Nat.Primrec.left).and hf').proj
  simp only [mem_toElementMap, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨X, hX, hfX⟩
    obtain ⟨n, rfl⟩ := P.surj (x.sub hX)
    exact ⟨n, hX, hfX⟩
  · rintro ⟨n, hxn, hfn⟩
    exact ⟨P.X n, hxn, hfn⟩

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

/-- **The identity map is computable** (the identity half of Proposition 7.3). The relation
`Xₙ I Xₘ` is `Xₙ ⊆ Xₘ` (`incl_computable`), which is recursively *decidable*, hence recursively
enumerable. -/
theorem idMap_isComputable (P : ComputablePresentation V) :
    ComputableMap P P (idMap V) :=
  ⟨(RecDecidable.of_iff (fun t => by
    simp only [idMap_rel]
    exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, P.mem_X _, h⟩⟩)
    P.incl_computable).re⟩

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

end

end DomainTheory.NeighbourhoodSystems
end
