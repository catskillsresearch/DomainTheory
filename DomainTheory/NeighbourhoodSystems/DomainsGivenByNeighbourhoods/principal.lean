module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_4

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L256 DEFINITION 1.7 principal filter -/
/-- **Definition 1.7 (Scott 1981, PRG-19).** The *principal filter* `↑X` determined by a
neighbourhood `X ∈ 𝒟`:

`↑X = {Y ∈ 𝒟 ∣ X ⊆ Y}`.

These are Scott's *finite elements* of `|𝒟|`. The four filter conditions:

* `sub` is the first projection (`Y ∈ ↑X ⟹ Y ∈ 𝒟`);
* `master_mem` needs `X ⊆ Δ`, supplied by `V.sub_master` (Scott's `𝒟 ⊆ 𝒫(Δ)`);
* `inter_mem` uses `Set.subset_inter` (from `X ⊆ Y₁`, `X ⊆ Y₂`) with `X` itself as the
  consistency witness for `V.inter_mem`;
* `up_mem` is transitivity of `⊆`. -/
def principal {X : Set α} (hX : V.mem X) : V.Element where
  mem Y := V.mem Y ∧ X ⊆ Y
  sub h := h.1
  master_mem := ⟨V.master_mem, V.sub_master hX⟩
  inter_mem h1 h2 :=
    ⟨V.inter_mem h1.1 h2.1 hX (Set.subset_inter h1.2 h2.2), Set.subset_inter h1.2 h2.2⟩
  up_mem h hY hsub := ⟨hY, h.2.trans hsub⟩

@[simp] theorem mem_principal {X Y : Set α} (hX : V.mem X) :
    (V.principal hX).mem Y ↔ V.mem Y ∧ X ⊆ Y := Iff.rfl
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
