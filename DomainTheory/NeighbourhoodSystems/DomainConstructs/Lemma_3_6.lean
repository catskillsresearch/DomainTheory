module
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_1
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
open ApproximableMap
/- concordance: source L1094 LEMMA 3.6 constant functions -/
/-- **Lemma 3.6 (Scott 1981, PRG-19).** The constant map at `b : |𝒟₁|`: `X b Y ↔ Y ∈ b`. -/
def constMap (V₀ : NeighborhoodSystem α) (b : V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ b.mem Y
  rel_dom h := h.1
  rel_cod h := b.sub h.2
  master_rel := ⟨V₀.master_mem, b.master_mem⟩
  inter_right := by rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩; exact ⟨hX, b.inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hY⟩ _ hYY' hX' hY'
    exact ⟨hX', b.up_mem hY hY' hYY'⟩

@[simp] theorem constMap_rel {b : V₁.Element} {X : Set α} {Y : Set β} :
    (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y := Iff.rfl

@[simp] theorem toElementMap_constMap (b : V₁.Element) (x : V₀.Element) :
    (constMap V₀ b).toElementMap x = b := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, _, _, hbY⟩; exact hbY
  · intro hbY; exact ⟨V₀.master, x.master_mem, V₀.master_mem, hbY⟩

end
end DomainTheory.NeighbourhoodSystems
end
