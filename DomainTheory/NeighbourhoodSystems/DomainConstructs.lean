module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert

@[expose] public section

section
-- Exercise318/il.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Left tag `0a = some (inl a)`. -/
def il (a : α) : Option (α ⊕ β) := some (Sum.inl a)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- The tagged left copy `0X = {some (inl a) ∣ a ∈ X}`. -/
def inj₀ (X : Set α) : Set (Option (α ⊕ β)) := il '' X

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/il_mem_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem il_mem_inj₀ {X : Set α} {a : α} : (il a : Option (α ⊕ β)) ∈ inj₀ X ↔ a ∈ X := by
  simp only [inj₀, Set.mem_image, il]
  constructor
  · rintro ⟨a', ha', hb⟩; simp only [Option.some.injEq, Sum.inl.injEq] at hb; exact hb ▸ ha'
  · intro ha; exact ⟨a, ha, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/ir.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Right tag `1b = some (inr b)`. -/
def ir (b : β) : Option (α ⊕ β) := some (Sum.inr b)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- The tagged right copy `1Y = {some (inr b) ∣ b ∈ Y}`. -/
def inj₁ (Y : Set β) : Set (Option (α ⊕ β)) := ir '' Y

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/ir_mem_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem ir_mem_inj₀ {X : Set α} {b : β} : (ir b : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il, ir])

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/none_mem_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem none_mem_inj₀ {X : Set α} : (none : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il])

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/ir_mem_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem ir_mem_inj₁ {Y : Set β} {b : β} : (ir b : Option (α ⊕ β)) ∈ inj₁ Y ↔ b ∈ Y := by
  simp only [inj₁, Set.mem_image, ir]
  constructor
  · rintro ⟨b', hb', hb⟩; simp only [Option.some.injEq, Sum.inr.injEq] at hb; exact hb ▸ hb'
  · intro hb; exact ⟨b, hb, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/il_mem_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem il_mem_inj₁ {Y : Set β} {a : α} : (il a : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [il, ir])

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/none_mem_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem none_mem_inj₁ {Y : Set β} : (none : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [ir])

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₀_inter (X X' : Set α) :
    (inj₀ X ∩ inj₀ X' : Set (Option (α ⊕ β))) = inj₀ (X ∩ X') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, il, inj₀]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀_inter_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₀_inter_inj₁ (X : Set α) (Y : Set β) :
    (inj₀ X ∩ inj₁ Y : Set (Option (α ⊕ β))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro t ⟨ht0, ht1⟩
  rcases t with _ | (a | b)
  · exact none_mem_inj₀ ht0
  · exact il_mem_inj₁ ht1
  · exact ir_mem_inj₀ ht0

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₀_nonempty {X : Set α} (hX : X.Nonempty) : (inj₀ X : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image il hX

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀_subset_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₀_subset_inj₀ {X X' : Set α} :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₀ X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact il_mem_inj₀.mp (h (il_mem_inj₀.mpr ha))
  · intro h t ht
    rw [inj₀, Set.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact il_mem_inj₀.mpr (h ha)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₁_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_inter (Y Y' : Set β) :
    (inj₁ Y ∩ inj₁ Y' : Set (Option (α ⊕ β))) = inj₁ (Y ∩ Y') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, ir, inj₁]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₁_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_nonempty {Y : Set β} (hY : Y.Nonempty) : (inj₁ Y : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image ir hY

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₁_subset_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_subset_inj₁ {Y Y' : Set β} :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₁ Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact ir_mem_inj₁.mp (h (ir_mem_inj₁.mpr hb))
  · intro h t ht
    rw [inj₁, Set.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact ir_mem_inj₁.mpr (h hb)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

/-- The master neighbourhood of the sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
def sumMaster : Set (Option (α ⊕ β)) := insert none (inj₀ V₀.master ∪ inj₁ V₁.master)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/none_mem_sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem none_mem_sumMaster : (none : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ :=
  Set.mem_insert _ _

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/il_injective.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem il_injective : Function.Injective (il : α → Option (α ⊕ β)) := by
  intro a a' h; simpa [il] using h

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/il_preimage_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem il_preimage_inj₀ (X : Set α) :
    ((il : α → Option (α ⊕ β)) ⁻¹' inj₀ X) = X :=
  Set.preimage_image_eq X il_injective

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₀_subset_sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem inj₀_subset_sumMaster {X : Set α} (hX : V₀.mem X) :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _ ?_))
  exact (inj₀_subset_inj₀.mpr (V₀.sub_master hX)) ht

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inj₁_subset_sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem inj₁_subset_sumMaster {Y : Set β} (hY : V₁.mem Y) :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ ?_))
  exact (inj₁_subset_inj₁.mpr (V₁.sub_master hY)) ht

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/ir_injective.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem ir_injective : Function.Injective (ir : β → Option (α ⊕ β)) := by
  intro b b' h; simpa [ir] using h

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/ir_preimage_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem ir_preimage_inj₁ (Y : Set β) :
    ((ir : β → Option (α ⊕ β)) ⁻¹' inj₁ Y) = Y :=
  Set.preimage_image_eq Y ir_injective

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

/-- The left content `leftPart W ⊆ Δ₀` of a sum-neighbourhood `W`: the `0`-tagged tokens of `W`,
*plus* all of `Δ₀` whenever `W` reaches into the right copy or the basepoint (so non-left
neighbourhoods contribute only `Δ₀`, i.e. project to `⊥`). This is a genuine (choice-free) function
of `W`. -/
def leftPart (V₀ : NeighborhoodSystem α) (W : Set (Option (α ⊕ β))) : Set α :=
  il ⁻¹' W ∪ {a | a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/mem_leftPart.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem mem_leftPart {V₀ : NeighborhoodSystem α} {W : Set (Option (α ⊕ β))} {a : α} :
    a ∈ leftPart V₀ W ↔ il a ∈ W ∨ (a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ none ∈ W)) := by
  simp only [leftPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

/-- The right content `rightPart W ⊆ Δ₁`, symmetric to `leftPart`. -/
def rightPart (V₁ : NeighborhoodSystem β) (W : Set (Option (α ⊕ β))) : Set β :=
  ir ⁻¹' W ∪ {b | b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/mem_rightPart.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem mem_rightPart {V₁ : NeighborhoodSystem β} {W : Set (Option (α ⊕ β))} {b : β} :
    b ∈ rightPart V₁ W ↔ ir b ∈ W ∨ (b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ none ∈ W)) := by
  simp only [rightPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem leftPart_inj₀ (V₀ : NeighborhoodSystem α) (X : Set α) :
    leftPart V₀ (inj₀ X : Set (Option (α ⊕ β))) = X := by
  ext a
  simp only [mem_leftPart, il_mem_inj₀, ir_mem_inj₀, none_mem_inj₀, exists_false, or_self,
    and_false]
  exact ⟨fun h => h.resolve_right (by simp), fun h => Or.inl h⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem leftPart_mono (V₀ : NeighborhoodSystem α) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    leftPart V₀ W ⊆ leftPart V₀ W' := by
  intro a ha
  rw [mem_leftPart] at ha ⊢
  exact ha.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨b, hb⟩ => ⟨b, h hb⟩) (fun hn => h hn)⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem rightPart_inj₁ (V₁ : NeighborhoodSystem β) (Y : Set β) :
    rightPart V₁ (inj₁ Y : Set (Option (α ⊕ β))) = Y := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₁, il_mem_inj₁, none_mem_inj₁, exists_false, or_self,
    and_false]
  exact ⟨fun h => h.resolve_right (by simp), fun h => Or.inl h⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem leftPart_inj₁ (V₀ : NeighborhoodSystem α) {Y : Set β} (hY : Y.Nonempty) :
    leftPart V₀ (inj₁ Y : Set (Option (α ⊕ β))) = V₀.master := by
  ext a
  simp only [mem_leftPart, il_mem_inj₁, none_mem_inj₁, or_false, false_or]
  constructor
  · rintro ⟨ha, _⟩; exact ha
  · intro ha; obtain ⟨b, hb⟩ := hY; exact ⟨ha, ⟨b, ir_mem_inj₁.mpr hb⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart_sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem leftPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    leftPart V₀ (sumMaster V₀ V₁) = V₀.master := by
  ext a
  simp only [mem_leftPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (il a : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [il])
      · rcases h' with h'' | h''
        · exact (il_mem_inj₀).mp h''
        · exact absurd h'' (by simp)
    · exact h
  · intro ha; exact Or.inr ha

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_inj₀ (V₁ : NeighborhoodSystem β) {X : Set α} (hX : X.Nonempty) :
    rightPart V₁ (inj₀ X : Set (Option (α ⊕ β))) = V₁.master := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₀, none_mem_inj₀, or_false, false_or]
  constructor
  · rintro ⟨hb, _⟩; exact hb
  · intro hb; obtain ⟨a, ha⟩ := hX; exact ⟨hb, ⟨a, il_mem_inj₀.mpr ha⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_mono (V₁ : NeighborhoodSystem β) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    rightPart V₁ W ⊆ rightPart V₁ W' := by
  intro b hb
  rw [mem_rightPart] at hb ⊢
  exact hb.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨a, ha⟩ => ⟨a, h ha⟩) (fun hn => h hn)⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart_sumMaster.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    rightPart V₁ (sumMaster V₀ V₁) = V₁.master := by
  ext b
  simp only [mem_rightPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (ir b : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [ir])
      · rcases h' with h'' | h''
        · exact absurd h'' (by simp)
        · exact (ir_mem_inj₁).mp h''
    · exact h
  · intro hb; exact Or.inr hb

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/sumMaster_inter_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem sumMaster_inter_inj₀ {X : Set α} (hX : V₀.mem X) :
    (sumMaster V₀ V₁ ∩ inj₀ X : Set (Option (α ⊕ β))) = inj₀ X :=
  Set.inter_eq_right.mpr (inj₀_subset_sumMaster hX)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/sumMaster_inter_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem sumMaster_inter_inj₁ {Y : Set β} (hY : V₁.mem Y) :
    (sumMaster V₀ V₁ ∩ inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y :=
  Set.inter_eq_right.mpr (inj₁_subset_sumMaster hY)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/sum.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The *sum system* `𝒟₀ + 𝒟₁` over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`,
under the standing assumption that no neighbourhood of `𝒟₀` or `𝒟₁` is empty. -/
def sum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem (Option (α ⊕ β)) where
  mem W := W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨ (∃ Y, V₁.mem Y ∧ W = inj₁ Y)
  master := sumMaster V₀ V₁
  master_nonempty := ⟨none, none_mem_sumMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact subset_rfl
    · exact inj₀_subset_sumMaster hX
    · exact inj₁_subset_sumMaster hY
  inter_mem := by
    -- every neighbourhood is non-empty, hence so is any consistency witness `Z`
    have hne : ∀ W, (W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨
        (∃ Y, V₁.mem Y ∧ W = inj₁ Y)) → (W : Set (Option (α ⊕ β))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨none, none_mem_sumMaster⟩
      · exact inj₀_nonempty (h₀ X hX)
      · exact inj₁_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumMaster_inter_inj₀ hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [sumMaster_inter_inj₁ hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₀ hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [inj₀_inter] at hZsub ⊢
        -- witness `Z ⊆ inj₀ (X ∩ X')`; `Z` non-empty forces it to be a left copy `inj₀ Z₀`
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₀
        · refine Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ₀ (inj₀_subset_inj₀.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          exact absurd (hZsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · rw [inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₁ hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
      · rw [Set.inter_comm, inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [inj₁_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₁
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          exact absurd (hZsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
        · refine Or.inr (Or.inr ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ₁ (inj₁_subset_inj₁.mp hZsub), rfl⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inMap₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left injection `in₀ : 𝒟₀ → 𝒟₀ + 𝒟₁`,
`X (in₀) W ↔ 0X ⊆ W`. -/
def inMap₀ : ApproximableMap V₀ (sum V₀ V₁ h₀ h₁) where
  rel X W := V₀.mem X ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inMap₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right injection `in₁ : 𝒟₁ → 𝒟₀ + 𝒟₁`. -/
def inMap₁ : ApproximableMap V₁ (sum V₀ V₁ h₀ h₁) where
  rel Y W := V₁.mem Y ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₁ Y ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₁.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
  inter_right := by
    rintro Y W W' ⟨hY, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hY, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro Y Y' W W' ⟨_, _, hsub⟩ hY'Y hWW' hY' hW'
    exact ⟨hY', hW', (inj₁_subset_inj₁.mpr hY'Y).trans (hsub.trans hWW')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/leftPart_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem leftPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₀.mem (leftPart V₀ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [leftPart_sumMaster]; exact V₀.master_mem
  · rw [leftPart_inj₀]; exact hX
  · rw [leftPart_inj₁ V₀ (h₁ Y hY)]; exact V₀.master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/outMap₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left projection `out₀ : 𝒟₀ + 𝒟₁ → 𝒟₀`,
`W (out₀) X ↔ leftPart W ⊆ X` (right/basepoint neighbourhoods relate only to `Δ₀`). -/
def outMap₀ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₀ where
  rel W X := (sum V₀ V₁ h₀ h₁).mem W ∧ V₀.mem X ∧ leftPart V₀ W ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V₀.inter_mem hX hX' (leftPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', (leftPart_mono V₀ hW'W).trans (hsub.trans hXX')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/rightPart_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem rightPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₁.mem (rightPart V₁ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [rightPart_sumMaster]; exact V₁.master_mem
  · rw [rightPart_inj₀ V₁ (h₀ X hX)]; exact V₁.master_mem
  · rw [rightPart_inj₁]; exact hY

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/outMap₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right projection `out₁ : 𝒟₀ + 𝒟₁ → 𝒟₁`. -/
def outMap₁ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₁ where
  rel W Y := (sum V₀ V₁ h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hW, V₁.inter_mem hY hY' (rightPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inju2080_injective.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


theorem inj₀_injective {X X' : Set α} (h : (inj₀ X : Set (Option (α ⊕ β))) = inj₀ X') : X = X' :=
  Set.Subset.antisymm (inj₀_subset_inj₀.mp h.subset) (inj₀_subset_inj₀.mp h.symm.subset)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/inju2081_injective.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


theorem inj₁_injective {Y Y' : Set β} (h : (inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y') : Y = Y' :=
  Set.Subset.antisymm (inj₁_subset_inj₁.mp h.subset) (inj₁_subset_inj₁.mp h.symm.subset)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/outMapu2080_comp_inMapu2080.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)


variable {V₀ V₁}


variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₀ ∘ in₀ = I_{𝒟₀}`. -/
theorem outMap₀_comp_inMap₀ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₀ = idMap V₀ := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, hZ, ?_⟩
    have hXW : X ⊆ leftPart V₀ W := by
      intro a ha
      rw [mem_leftPart]; exact Or.inl (hinj (il_mem_inj₀.mpr ha))
    exact hXW.trans hsub
  · rintro ⟨hX, hZ, hXZ⟩
    refine ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), hZ, ?_⟩
    rw [leftPart_inj₀]; exact hXZ

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318/outMapu2081_comp_inMapu2081.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)


variable {V₀ V₁}


variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₁ ∘ in₁ = I_{𝒟₁}`. -/
theorem outMap₁_comp_inMap₁ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₁ = idMap V₁ := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, hZ, ?_⟩
    have hYW : Y ⊆ rightPart V₁ W := by
      intro b hb
      rw [mem_rightPart]; exact Or.inl (hinj (ir_mem_inj₁.mpr hb))
    exact hYW.trans hsub
  · rintro ⟨hY, hZ, hYZ⟩
    refine ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), hZ, ?_⟩
    rw [rightPart_inj₁]; exact hYZ

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise318.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_318.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V₀ V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) α V₀
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β V₁ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) β V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β V₁)) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V₀ V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) α V₀
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β V₁ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) β V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β V₁))
  @DomainTheory.NeighbourhoodSystems.outMap₀_comp_inMap₀ @DomainTheory.NeighbourhoodSystems.outMap₁_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/eq_sumMaster_of_subset.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A sum-neighbourhood that *contains* the master is the master. -/
theorem eq_sumMaster_of_subset {W : Set (Option (α ⊕ β))}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : sumMaster V₀ V₁ ⊆ W) :
    W = sumMaster V₀ V₁ :=
  Set.Subset.antisymm ((sum V₀ V₁ h₀ h₁).sub_master hW) hsub

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/mem_subset_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A sum-neighbourhood contained in a *left* copy `0X` is itself a left copy `0X₂` (the basepoint and
the right copy are excluded, using non-emptiness). -/
theorem mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/mem_subset_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A sum-neighbourhood contained in a *right* copy `1Y` is itself a right copy `1Y₂`. -/
theorem mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/not_inj₀_subset_inj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A nonempty left copy is never contained in a right copy. -/
theorem not_inj₀_subset_inj₁ {X : Set α} {Y : Set β} (hX : X.Nonempty)
    (hsub : (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₁ Y) : False := by
  obtain ⟨a, ha⟩ := hX
  exact il_mem_inj₁ (hsub (il_mem_inj₀.mpr ha))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/not_inj₁_subset_inj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A nonempty right copy is never contained in a left copy. -/
theorem not_inj₁_subset_inj₀ {X : Set α} {Y : Set β} (hY : Y.Nonempty)
    (hsub : (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₀ X) : False := by
  obtain ⟨b, hb⟩ := hY
  exact ir_mem_inj₀ (hsub (ir_mem_inj₁.mpr hb))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/sumMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- **Exercise 3.19 (Scott 1981, PRG-19).** The *sum mapping* `f + g : 𝒟₀ + 𝒟₁ → 𝒟₀' + 𝒟₁'`. As a
relation between sum-neighbourhoods, `W (f+g) W'` holds iff `W'` is the codomain master, or `W = 0X`
with `W' = 0Y'` and `X f Y'`, or `W = 1Y` with `W' = 1Y'` and `Y g Y'`. -/
def sumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (sum V₀ V₁ h₀ h₁) (sum V₀' V₁' h₀' h₁') where
  rel W W' := (sum V₀ V₁ h₀ h₁).mem W ∧ (sum V₀' V₁' h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, (sum V₀' V₁' h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    -- membership of any disjunction-satisfying set
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ g.rel Y Y')) →
          (sum V₀' V₁' h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hg⟩)
      · exact (sum V₀' V₁' h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, rfl⟩)
    -- the disjunction is preserved by intersection
    have key : (W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ g.rel Y Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩
      · rw [Set.inter_eq_right.mpr
          (show W'₂ ⊆ sumMaster V₀' V₁' from (sum V₀' V₁' h₀' h₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f.inter_right hf₁ hf₂⟩)
        · exact absurd ((hWX₁.symm.trans hWY₂)) (fun h =>
            not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩)
        · exact absurd ((hWY₁.symm.trans hWX₂)) (fun h =>
            not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hg⟩
    · -- W' = master; W'₂ ⊇ master so W'₂ = master
      left; exact eq_sumMaster_of_subset hW'₂mem hW'W'₂
    · -- left copy: W₂ ⊆ 0X, W'₂ ⊇ 0Y'
      obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Z'₂, hZ'₂, rfl⟩
      · left; rfl
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₀_subset_inj₀.mp hW'W'₂
        exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f.mono hf hXX₂ hY'Y'₂ hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · -- right copy: W₂ ⊆ 1Y, W'₂ ⊇ 1Y'
      obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₁_subset_inj₁.mp hW'W'₂
        exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl,
          g.mono hg hYY₂ hY'Y'₂ hY₂ hY'₂⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/outMapu2080_comp_sumMap_comp_inMapu2080.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}


/-- **Exercise 3.19(iii) (Scott 1981, PRG-19).** `out₀ ∘ (f + g) ∘ in₀ = f`. -/
theorem outMap₀_comp_sumMap_comp_inMap₀ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hX, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hleft⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · -- output master: leftPart = Δ₀', and Z ⊇ Δ₀' so Z = Δ₀'
      rw [leftPart_sumMaster] at hleft
      have : Z = V₀'.master := Set.Subset.antisymm (V₀'.sub_master hZ) hleft
      subst this
      exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₀'.master_mem
    · -- output 0Y': X ⊆ X₀ and Y' ⊆ Z
      rw [leftPart_inj₀] at hleft
      have hXX₀ : X ⊆ X₀ := inj₀_subset_inj₀.mp (hWX₀ ▸ hinj)
      exact f.mono hf hXX₀ hleft hX hZ
    · -- impossible: in₀ forces 0X ⊆ W = 1Y₀
      exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY₀ ▸ hinj)).elim
  · intro hf
    refine ⟨inj₀ Z, ⟨inj₀ X, ⟨f.rel_dom hf, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, f.rel_cod hf, ?_⟩
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Z, rfl, rfl, hf⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact (leftPart_inj₀ V₀' Z).subset

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum/outMapu2081_comp_sumMap_comp_inMapu2081.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}


/-- **Exercise 3.19(iv) (Scott 1981, PRG-19).** `out₁ ∘ (f + g) ∘ in₁ = g`. -/
theorem outMap₁_comp_sumMap_comp_inMap₁ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hY, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hright⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · rw [rightPart_sumMaster] at hright
      have : Z = V₁'.master := Set.Subset.antisymm (V₁'.sub_master hZ) hright
      subst this
      exact g.mono g.master_rel (V₁.sub_master hY) subset_rfl hY V₁'.master_mem
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX₀ ▸ hinj)).elim
    · rw [rightPart_inj₁] at hright
      have hYY₀ : Y ⊆ Y₀ := inj₁_subset_inj₁.mp (hWY₀ ▸ hinj)
      exact g.mono hg hYY₀ hright hY hZ
  · intro hg
    refine ⟨inj₁ Z, ⟨inj₁ Y, ⟨g.rel_dom hg, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, g.rel_cod hg, ?_⟩
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, Z, rfl, rfl, hg⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact (rightPart_inj₁ V₁' Z).subset

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319Sum.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_319_sum.{u_1, u_2, u_3, u_4} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g)
  @DomainTheory.NeighbourhoodSystems.outMap₀_comp_sumMap_comp_inMap₀
  @DomainTheory.NeighbourhoodSystems.outMap₁_comp_sumMap_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodNbhd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- The product neighbourhood `X ∪ Y` over the disjoint union `Δ₀ ∪ Δ₁`, modelled on `α ⊕ β` as
`Sum.inl '' X ∪ Sum.inr '' Y`. -/
def prodNbhd (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_prodNbhd_inl.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem mem_prodNbhd_inl {X : Set α} {Y : Set β} {a : α} :
    (Sum.inl a : α ⊕ β) ∈ prodNbhd X Y ↔ a ∈ X := by
  simp [prodNbhd]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_prodNbhd_inr.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem mem_prodNbhd_inr {X : Set α} {Y : Set β} {b : β} :
    (Sum.inr b : α ⊕ β) ∈ prodNbhd X Y ↔ b ∈ Y := by
  simp [prodNbhd]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/inl_preimage_prodNbhd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem inl_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inl ⁻¹' prodNbhd X Y = X := by ext a; simp

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/inr_preimage_prodNbhd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem inr_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inr ⁻¹' prodNbhd X Y = Y := by ext b; simp

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodNbhd_injective.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- The representation `X ∪ Y` is unique (choice-free, via the preimage projections). -/
theorem prodNbhd_injective {X X' : Set α} {Y Y' : Set β}
    (h : prodNbhd X Y = prodNbhd X' Y') : X = X' ∧ Y = Y' := by
  refine ⟨?_, ?_⟩
  · rw [← inl_preimage_prodNbhd X Y, ← inl_preimage_prodNbhd X' Y', h]
  · rw [← inr_preimage_prodNbhd X Y, ← inr_preimage_prodNbhd X' Y', h]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodNbhd_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- Scott's (2): the product nbhds intersect componentwise. -/
theorem prodNbhd_inter (X X' : Set α) (Y Y' : Set β) :
    prodNbhd X Y ∩ prodNbhd X' Y' = prodNbhd (X ∩ X') (Y ∩ Y') := by
  ext (a | b) <;> simp [Set.mem_inter_iff]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodNbhd_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- Scott's (1): inclusion of product nbhds is componentwise (uses disjointness of `Δ₀`, `Δ₁`). -/
theorem prodNbhd_subset_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y ⊆ prodNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have : (Sum.inl a : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using ha)
      simpa using this
    · have : (Sum.inr b : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using hb)
      simpa using this
  · rintro ⟨hX, hY⟩ (a | b) hs
    · simp only [mem_prodNbhd_inl] at hs ⊢; exact hX hs
    · simp only [mem_prodNbhd_inr] at hs ⊢; exact hY hs

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- **Definition 3.1 (Scott 1981, PRG-19).** The *product system* `𝒟₀ × 𝒟₁`: neighbourhoods are
`X ∪ Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closure under consistent intersection is Scott's (2)
(`prodNbhd_inter`) together with the factors' closure; the consistency witness `Z ⊆ (X∪Y) ∩ (X'∪Y')`
splits into witnesses `Z₀ ⊆ X ∩ X'`, `Z₁ ⊆ Y ∩ Y'` by `prodNbhd_subset_iff`. -/
def prod (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := ⟨V₀.master, V₁.master, V₀.master_mem, V₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', V₀.inter_mem hX hX' hZ₀ hsub₀, V₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod_mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prod_mem_iff {W : Set (α ⊕ β)} :
    (prod V₀ V₁).mem W ↔ ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prod_master : (prod V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod_mem_prodNbhd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem prod_mem_prodNbhd {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (prod V₀ V₁).mem (prodNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/fst.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's `z₀ = {X ∈ 𝒟₀ ∣ X ∪ Δ₁ ∈ z}`: the first component of a product element. -/
def NeighborhoodSystem.Element.fst (z : (prod V₀ V₁).Element) : V₀.Element where
  mem X := V₀.mem X ∧ z.mem (prodNbhd X V₁.master)
  sub h := h.1
  master_mem := ⟨V₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    refine ⟨hX', z.up_mem hzX (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_fst.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_fst {z : (prod V₀ V₁).Element} {X : Set α} :
    z.fst.mem X ↔ V₀.mem X ∧ z.mem (prodNbhd X V₁.master) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/snd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's `z₁ = {Y ∈ 𝒟₁ ∣ Δ₀ ∪ Y ∈ z}`: the second component of a product element. -/
def NeighborhoodSystem.Element.snd (z : (prod V₀ V₁).Element) : V₁.Element where
  mem Y := V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y)
  sub h := h.1
  master_mem := ⟨V₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    refine ⟨hY', z.up_mem hzY (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_snd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_snd {z : (prod V₀ V₁).Element} {Y : Set β} :
    z.snd.mem Y ↔ V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/pair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Definition 3.1 (Scott 1981, PRG-19).** The element pairing `⟨x, y⟩ = {X ∪ Y ∣ X ∈ x, Y ∈ y}`. -/
def pair (x : V₀.Element) (y : V₁.Element) : (prod V₀ V₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prod_mem_prodNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_pair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_pair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (pair x y).mem W ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/mem_pair_prodNbhd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem mem_pair_prodNbhd {x : V₀.Element} {y : V₁.Element} {X : Set α} {Y : Set β} :
    (pair x y).mem (prodNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/fst_pair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem fst_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).fst = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).1
  · intro hX
    exact ⟨x.sub hX, mem_pair_prodNbhd.mpr ⟨hX, y.master_mem⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod_mem_split.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The key splitting (Scott's (3)): for a product element `z` and neighbourhoods `X ∈ 𝒟₀`,
`Y ∈ 𝒟₁`, membership of `X ∪ Y` in `z` is equivalent to membership of its two "slices". -/
theorem prod_mem_split {z : (prod V₀ V₁).Element} {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    z.mem (prodNbhd X Y) ↔ z.mem (prodNbhd X V₁.master) ∧ z.mem (prodNbhd V₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prod_mem_prodNbhd hX V₁.master_mem) ?_,
            z.up_mem h (prod_mem_prodNbhd V₀.master_mem hY) ?_⟩
    · exact prodNbhd_subset_iff.mpr ⟨subset_rfl, V₁.sub_master hY⟩
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
      Set.inter_eq_right.mpr (V₁.sub_master hY)] at this

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/pair_fst_snd.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `z = ⟨z₀, z₁⟩`: every product element is the pairing of its two components. -/
theorem pair_fst_snd (z : (prod V₀ V₁).Element) : pair z.fst z.snd = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prod_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prod_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/snd_pair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem snd_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).snd = y := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).2
  · intro hY
    exact ⟨y.sub hY, mem_pair_prodNbhd.mpr ⟨x.master_mem, hY⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Proposition 3.2 (Scott 1981, PRG-19).** The order-isomorphism `|𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`. -/
def prodEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o V₀.Element × V₁.Element where
  toFun z := (z.fst, z.snd)
  invFun p := pair p.1 p.2
  left_inv z := pair_fst_snd z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prod_mem_split hX hY).mp hW
      have hX' : z'.fst.mem X := h1 X ⟨hX, ha⟩
      have hY' : z'.snd.mem Y := h2 Y ⟨hY, hb⟩
      exact (prod_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodEquiv_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prodEquiv_apply (z : (prod V₀ V₁).Element) :
    prodEquiv V₀ V₁ z = (z.fst, z.snd) := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodEquiv_symm_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prodEquiv_symm_apply (p : V₀.Element × V₁.Element) :
    (prodEquiv V₀ V₁).symm p = pair p.1 p.2 := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prodNbhd_preimage.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- Every product neighbourhood is `(inl⁻¹ W) ∪ (inr⁻¹ W)`. -/
theorem prodNbhd_preimage {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) :
    W = prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, _, rfl⟩ := hW
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/paired.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Definition 3.3 (Scott 1981, PRG-19).** The paired mapping `⟨f, g⟩ : 𝒟₂ → 𝒟₀ × 𝒟₁`,
`Z ⟨f, g⟩ (X ∪ Y) ↔ Z f X ∧ Z g Y`. -/
def paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    ApproximableMap V₂ (prod V₀ V₁) where
  rel Z P := (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P)
  rel_dom h := f.rel_dom h.2.1
  rel_cod h := h.1
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_, ?_⟩
    · simpa using f.master_rel
    · simpa using g.master_rel
  inter_right := by
    rintro Z P P' ⟨hP, hfP, hgP⟩ ⟨hP', hfP', hgP'⟩
    have hfX := f.inter_right hfP hfP'
    have hgY := g.inter_right hgP hgP'
    refine ⟨?_, ?_, ?_⟩
    · rw [prodNbhd_preimage hP, prodNbhd_preimage hP', prodNbhd_inter]
      exact prod_mem_prodNbhd (f.rel_cod hfX) (g.rel_cod hgY)
    · rw [Set.preimage_inter]; exact hfX
    · rw [Set.preimage_inter]; exact hgY
  mono := by
    rintro Z Z₂ P P₂ ⟨_, hfP, hgP⟩ hZ₂Z hPP₂ hZ₂ hP₂
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₂
    have hinl : Sum.inl ⁻¹' P ⊆ A := by
      have := Set.preimage_mono (f := Sum.inl) hPP₂; rwa [inl_preimage_prodNbhd] at this
    have hinr : Sum.inr ⁻¹' P ⊆ B := by
      have := Set.preimage_mono (f := Sum.inr) hPP₂; rwa [inr_preimage_prodNbhd] at this
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]; exact f.mono hfP hZ₂Z hinl hZ₂ hA
    · rw [inr_preimage_prodNbhd]; exact g.mono hgP hZ₂Z hinr hZ₂ hB

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₀ : 𝒟₀ × 𝒟₁ → 𝒟₀`,
`(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def proj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₀ where
  rel W X' := (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨_, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, hA, ‹_›, rfl⟩, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proj₀_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem proj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (proj₀ V₀ V₁).rel W X' ↔ (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₁ : 𝒟₀ × 𝒟₁ → 𝒟₁`,
`(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def proj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₁ where
  rel W Y' := (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨_, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, ‹_›, hB, rfl⟩, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proj₁_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem proj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (proj₁ V₀ V₁).rel W Y' ↔ (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/paired_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem paired_rel {f : ApproximableMap V₂ V₀} {g : ApproximableMap V₂ V₁}
    {Z : Set γ} {P : Set (α ⊕ β)} :
    (paired f g).rel Z P ↔
      (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toElementMap_proj₀.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem toElementMap_proj₀ (z : (prod V₀ V₁).Element) :
    (proj₀ V₀ V₁).toElementMap z = z.fst := by
  apply Element.ext
  intro X'
  constructor
  · rintro ⟨W, hzW, hW, hX', hsub⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub
    refine ⟨hX', z.up_mem hzW (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hsub, V₁.sub_master hB⟩
  · rintro ⟨hX', hz⟩
    exact ⟨prodNbhd X' V₁.master, hz, prod_mem_prodNbhd hX' V₁.master_mem, hX', by simp⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toElementMap_proj₁.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem toElementMap_proj₁ (z : (prod V₀ V₁).Element) :
    (proj₁ V₀ V₁).toElementMap z = z.snd := by
  apply Element.ext
  intro Y'
  constructor
  · rintro ⟨W, hzW, hW, hY', hsub⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub
    refine ⟨hY', z.up_mem hzW (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hA, hsub⟩
  · rintro ⟨hY', hz⟩
    exact ⟨prodNbhd V₀.master Y', hz, prod_mem_prodNbhd V₀.master_mem hY', hY', by simp⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/constMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

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

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/constMap_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem constMap_rel {b : V₁.Element} {X : Set α} {Y : Set β} :
    (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/prod_mem_prodNbhd_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

theorem prod_mem_prodNbhd_iff {X : Set α} {Y : Set β} :
    (prod V₀ V₁).mem (prodNbhd X Y) ↔ V₀.mem X ∧ V₁.mem Y := by
  constructor
  · rintro ⟨A, B, hA, hB, heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hB⟩
  · rintro ⟨hX, hY⟩; exact prod_mem_prodNbhd hX hY

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toElementMap_constMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

@[simp] theorem toElementMap_constMap (b : V₁.Element) (x : V₀.Element) :
    (constMap V₀ b).toElementMap x = b := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, _, _, hbY⟩; exact hbY
  · intro hbY; exact ⟨V₀.master, x.master_mem, V₀.master_mem, hbY⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/ext.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- Extensionality for two-variable approximable mappings. -/
theorem ApproximableMap₂.ext {f g : ApproximableMap₂ V₀ V₁ V₂}
    (h : ∀ X Y Z, f.rel X Y Z ↔ g.rel X Y Z) : f = g := by
  obtain ⟨rf, _, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y Z; exact propext (h X Y Z)
  subst this; rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/ofMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Theorem 3.5 (←) (Scott 1981, PRG-19).** A two-variable mapping induces a joint mapping. -/
def ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ f.rel (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) Z
  rel_dom h := h.1
  rel_cod h := f.rel_cod h.2
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    simpa using f.master_rel
  inter_right := by rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩; exact ⟨hW, f.inter_right hrel hrel'⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl
    rw [inr_preimage_prodNbhd] at hinr
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact f.mono hrel hinl hinr hZZ' hA hB hZ'

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Theorem 3.5 (→) (Scott 1981, PRG-19).** A joint approximable mapping `𝒟₀ × 𝒟₁ → 𝒟₂`
restricts to a two-variable mapping `X, Y f Z ↔ (X ∪ Y) f Z`. -/
def toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap₂ V₀ V₁ V₂ where
  rel X Y Z := f.rel (prodNbhd X Y) Z
  rel_dom₀ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).1
  rel_dom₁ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).2
  rel_cod h := f.rel_cod h
  master_rel := f.master_rel
  inter_right h h' := f.inter_right h h'
  mono := by
    rintro X X' Y Y' Z Z' hrel hX'X hY'Y hZZ' hX' hY' hZ'
    exact f.mono hrel (prodNbhd_subset_iff.mpr ⟨hX'X, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX' hY') hZ'

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/ofMap₂_toMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

theorem ofMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ofMap₂ (toMap₂ f) = f := by
  apply ApproximableMap.ext
  intro W Z
  show (prod V₀ V₁).mem W ∧ f.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z ↔ _
  constructor
  · rintro ⟨hW, hrel⟩; rwa [← prodNbhd_preimage hW] at hrel
  · intro hrel
    exact ⟨f.rel_dom hrel, by rwa [← prodNbhd_preimage (f.rel_dom hrel)]⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toMap₂_ofMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

theorem toMap₂_ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : toMap₂ (ofMap₂ f) = f := by
  apply ApproximableMap₂.ext
  intro X Y Z
  show (prod V₀ V₁).mem (prodNbhd X Y) ∧ f.rel _ _ Z ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, hrel⟩; exact hrel
  · intro hrel
    exact ⟨prod_mem_prodNbhd (f.rel_dom₀ hrel) (f.rel_dom₁ hrel), hrel⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/map₂Equiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Theorem 3.5 (Scott 1981, PRG-19).** The bijection between joint approximable mappings
`𝒟₀ × 𝒟₁ → 𝒟₂` and two-variable mappings `𝒟₀, 𝒟₁ → 𝒟₂`: a function of two arguments comes from
an approximable mapping iff it is separately approximable. -/
def map₂Equiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃ ApproximableMap₂ V₀ V₁ V₂ where
  toFun := toMap₂
  invFun := ofMap₂
  left_inv := ofMap₂_toMap₂
  right_inv := toMap₂_ofMap₂

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/ApproximableMapu2erel_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- An approximable map relates any input neighbourhood to the master output `Δ₁`. -/
theorem ApproximableMap.rel_master (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) :
    f.rel X V₁.master :=
  f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/pair_le_pair_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Proposition 3.2(i) (Scott 1981, PRG-19).** `⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toElementMap_paired.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(iv) (Scott 1981, PRG-19).** `⟨f, g⟩(w) = ⟨f(w), g(w)⟩`. -/
theorem toElementMap_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁)
    (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) := by
  apply Element.ext
  intro P
  constructor
  · rintro ⟨Z, hwZ, hP, hfZ, hgZ⟩
    exact ⟨Sum.inl ⁻¹' P, Sum.inr ⁻¹' P, ⟨Z, hwZ, hfZ⟩, ⟨Z, hwZ, hgZ⟩, prodNbhd_preimage hP⟩
  · rintro ⟨X, Y, ⟨Z₁, hwZ₁, hfZ₁⟩, ⟨Z₂, hwZ₂, hgZ₂⟩, rfl⟩
    refine ⟨Z₁ ∩ Z₂, w.inter_mem hwZ₁ hwZ₂, prod_mem_prodNbhd (f.rel_cod hfZ₁) (g.rel_cod hgZ₂),
      ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]
      exact f.mono hfZ₁ Set.inter_subset_left subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (f.rel_cod hfZ₁)
    · rw [inr_preimage_prodNbhd]
      exact g.mono hgZ₂ Set.inter_subset_right subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (g.rel_cod hgZ₂)

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/paired_proj.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(iii) (Scott 1981, PRG-19).** `h = ⟨p₀ ∘ h, p₁ ∘ h⟩`. -/
theorem paired_proj (h : ApproximableMap V₂ (prod V₀ V₁)) :
    paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, pair_fst_snd]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proju2080_comp_paired.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₀ ∘ ⟨f, g⟩ = f`. -/
theorem proj₀_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired f g) = f := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, fst_pair]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/proju2081_comp_paired.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₁ ∘ ⟨f, g⟩ = g`. -/
theorem proj₁_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₁ V₀ V₁).comp (paired f g) = g := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₁, snd_pair]

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/toElementMapu2082_toMapu2082.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Theorem 3.5 (elementwise) (Scott 1981, PRG-19).** The two-variable elementwise map of
`toMap₂ f` is `f` evaluated at the pairing: `(toMap₂ f)(x, y) = f(⟨x, y⟩)`. -/
theorem toElementMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, hX, hY, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
    exact ⟨X, Y, hX, hY, hrel⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Product/substitution_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


variable {V₃ : NeighborhoodSystem δ}

/-- **Proposition 3.7 (Scott 1981, PRG-19).** Multivariate approximable functions are closed under
substitution: substituting approximable maps `a, b : 𝒟₃ → 𝒟ᵢ` into a two-variable approximable map
`F : 𝒟₀ × 𝒟₁ → 𝒟₂` yields the approximable map `F ∘ ⟨a, b⟩`, whose value is `F(a(w), b(w))`. The
building blocks are exactly Definition 3.3's `paired` and Theorem 2.5's `comp`. -/
theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise314/diag.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.14 (Scott 1981, PRG-19).** The *diagonal* approximable mapping
`diag : 𝒟 → 𝒟 × 𝒟`, defined as the paired map `⟨I_𝒟, I_𝒟⟩` of the identity with itself. -/
def diag : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise314/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


@[simp] theorem diag_rel {Z : Set α} {P : Set (α ⊕ α)} :
    (diag V).rel Z P ↔
      (prod V V).mem P ∧ (idMap V).rel Z (Sum.inl ⁻¹' P) ∧ (idMap V).rel Z (Sum.inr ⁻¹' P) :=
  Iff.rfl

@[simp] theorem toElementMap_diag (x : V.Element) :
    (diag V).toElementMap x = pair x x := by
  rw [diag, toElementMap_paired, toElementMap_idMap]
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise314/proju2080_comp_diag.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 3.14 (Scott 1981, PRG-19).** Post-composing the diagonal with the two projections
returns the identity: `p₀ ∘ diag = I` and `p₁ ∘ diag = I`. -/
theorem proj₀_comp_diag : (proj₀ V V).comp (diag V) = idMap V :=
  proj₀_comp_paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise314.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_314.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α α) α V
      (@DomainTheory.NeighbourhoodSystems.prod α α V V) V (@DomainTheory.NeighbourhoodSystems.proj₀ α α V V)
      (@DomainTheory.NeighbourhoodSystems.diag α V))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V) :=
  @DomainTheory.NeighbourhoodSystems.proj₀_comp_diag

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise314/proju2081_comp_diag.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


theorem proj₁_comp_diag : (proj₁ V V).comp (diag V) = idMap V :=
  proj₁_comp_paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodCommD.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15(i) (Scott 1981, PRG-19).** The commutativity order-isomorphism
`|𝒟₀ × 𝒟₁| ≃o |𝒟₁ × 𝒟₀|`, factored through Proposition 3.2 and the cartesian swap. -/
def prodCommD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o (prod V₁ V₀).Element :=
  (prodEquiv V₀ V₁).trans (OrderIso.prodComm.trans (prodEquiv V₁ V₀).symm)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodCongrOrderIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- The product of two order isomorphisms, as an order isomorphism. -/
def prodCongrOrderIso {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e₀ : A ≃o B) (e₁ : C ≃o D) : A × C ≃o B × D where
  toFun p := (e₀ p.1, e₁ p.2)
  invFun q := (e₀.symm q.1, e₁.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    show (e₀ a, e₁ c) ≤ (e₀ a', e₁ c') ↔ (a, c) ≤ (a', c')
    rw [Prod.mk_le_mk, Prod.mk_le_mk, e₀.le_iff_le, e₁.le_iff_le]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodAssocD.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15(ii) (Scott 1981, PRG-19).** The associativity order-isomorphism
`|𝒟₀ × (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ × 𝒟₁) × 𝒟₂|`. -/
def prodAssocD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (prod V₀ (prod V₁ V₂)).Element ≃o (prod (prod V₀ V₁) V₂).Element :=
  (prodEquiv V₀ (prod V₁ V₂)).trans <|
    (prodCongrOrderIso (OrderIso.refl V₀.Element) (prodEquiv V₁ V₂)).trans <|
      (OrderIso.prodAssoc V₀.Element V₁.Element V₂.Element).symm.trans <|
        (prodCongrOrderIso (prodEquiv V₀ V₁).symm (OrderIso.refl V₂.Element)).trans
          (prodEquiv (prod V₀ V₁) V₂).symm

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodUniqueOrderIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- For a `Unique` second factor, `A × C ≃o A` (forget the constant component). -/
def prodUniqueOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : A × C ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := by
    have : (default : C) = p.2 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨h, le_of_eq (Subsingleton.elim c c')⟩, And.left⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/uniqueProdOrderIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- For a `Unique` first factor, `C × A ≃o A` (forget the constant component). -/
def uniqueProdOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : C × A ≃o A where
  toFun p := p.2
  invFun a := (default, a)
  left_inv p := by
    have : (default : C) = p.1 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨c, a⟩ ⟨c', a'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨le_of_eq (Subsingleton.elim c c'), h⟩, And.right⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/unitSys.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- The **terminal domain** `𝟙`: the neighbourhood system over `Unit` with the single
neighbourhood `Δ = univ`. Its domain `|𝟙|` has exactly one element (`⊥ = {Δ}`), so `𝟙` is the
*product of no factors*. -/
def unitSys : NeighborhoodSystem Unit where
  mem X := X = Set.univ
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := rfl
  inter_mem := by rintro X Y Z rfl rfl _ _; simp
  sub_master := by rintro X rfl; exact subset_rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/unitSys_element_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- `|𝟙|` is a subsingleton: every element is `⊥`. -/
theorem unitSys_element_eq (x : unitSys.Element) : x = unitSys.bot := by
  apply Element.ext
  intro Y
  constructor
  · intro hY; rw [mem_bot]; exact x.sub hY
  · intro hY; rw [mem_bot] at hY; subst hY; exact x.master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/BasicInst12.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

instance : Unique unitSys.Element where
  default := unitSys.bot
  uniq := unitSys_element_eq

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodCongrD.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15(iii) (Scott 1981, PRG-19).** Two domain isomorphisms induce one on the products:
`|𝒟₀ × 𝒟₁| ≃o |𝒟₀' × 𝒟₁'|`. -/
def prodCongrD (e₀ : V₀.Element ≃o V₀'.Element) (e₁ : V₁.Element ≃o V₁'.Element) :
    (prod V₀ V₁).Element ≃o (prod V₀' V₁').Element :=
  (prodEquiv V₀ V₁).trans ((prodCongrOrderIso e₀ e₁).trans (prodEquiv V₀' V₁').symm)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prodUnitD.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/unitProdD.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/Isomorphicu2eprod.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prod_assoc_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prod_comm_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_315.{u_1, u_2, u_4, u_5, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
    @DomainTheory.NeighbourhoodSystems.prod_comm_isomorphic @DomainTheory.NeighbourhoodSystems.Isomorphic.prod)
  @DomainTheory.NeighbourhoodSystems.prod_assoc_isomorphic

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/prod_unit_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise315/unit_prod_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


theorem unit_prod_isomorphic : prod unitSys V₀ ≅ᴰ V₀ := ⟨unitProdD V₀⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- The `i`-th *fiber* of a set `W ⊆ ℕ × α`: the tokens appearing in copy `i`. -/
def fiber (W : Set (ℕ × α)) (i : ℕ) : Set α := {a | (i, a) ∈ W}

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/mem_fiber.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/eq_of_fiber_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem eq_of_fiber_eq {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i = fiber W' i) : W = W' := by
  ext ⟨i, a⟩
  exact Set.ext_iff.mp (h i) a

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem fiber_inter (W W' : Set (ℕ × α)) (i : ℕ) :
    fiber (W ∩ W') i = fiber W i ∩ fiber W' i := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem fiber_mono {W W' : Set (ℕ × α)} (h : W ⊆ W') (i : ℕ) : fiber W i ⊆ fiber W' i :=
  fun _ ha => h ha

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/single.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- The `𝒟^∞`-neighbourhood pinning copy `n` to `X` and leaving all other copies at `Δ`: Scott's
`Δ^∞ ∩ (1ⁿ0X)`, i.e. the combination with `Xₙ = X` and `Xₘ = Δ` for `m ≠ n`. -/
def single (n : ℕ) (X : Set α) : Set (ℕ × α) :=
  {p | if p.1 = n then p.2 ∈ X else p.2 ∈ V.master}

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber_single_self.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem fiber_single_self (n : ℕ) (X : Set α) : fiber (single V n X) n = X := by
  ext a; simp [fiber, single]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber_single_ne.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem fiber_single_ne {n i : ℕ} (h : i ≠ n) (X : Set α) : fiber (single V n X) i = V.master := by
  ext a; simp [fiber, single, h]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/iterSys.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The infinite iterate `𝒟^∞` over `Δ^∞ = ℕ × Δ`:
`W ∈ 𝒟^∞` iff every fiber is a neighbourhood of `𝒟` and all but finitely many fibers equal `Δ`. -/
def iterSys (V : NeighborhoodSystem α) : NeighborhoodSystem (ℕ × α) where
  mem W := (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master
  master := {p | p.2 ∈ V.master}
  master_nonempty := by
    obtain ⟨a, ha⟩ := V.master_nonempty
    exact ⟨(0, a), ha⟩
  master_mem := ⟨fun _ => V.master_mem, 0, fun _ _ => rfl⟩
  inter_mem := by
    rintro W W' Z ⟨hWf, NW, hNW⟩ ⟨hW'f, NW', hNW'⟩ ⟨hZf, _⟩ hsub
    refine ⟨fun i => ?_, max NW NW', fun i hi => ?_⟩
    · rw [fiber_inter]
      exact V.inter_mem (hWf i) (hW'f i) (hZf i) (fiber_mono hsub i)
    · rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  sub_master := by
    rintro W ⟨hWf, _⟩ ⟨i, a⟩ ha
    exact V.sub_master (hWf i) ha

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/iterSys_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem iterSys_master : (iterSys V).master = {p : ℕ × α | p.2 ∈ V.master} := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/fiber_iterSys_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem fiber_iterSys_master (i : ℕ) : fiber ((iterSys V).master) i = V.master := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/mem_iterSys.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem mem_iterSys {W : Set (ℕ × α)} :
    (iterSys V).mem W ↔ (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/interUpTo_subset_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem interUpTo_subset_master (F : ℕ → Set (ℕ × α)) (N : ℕ) :
    (iterSys V).interUpTo F N ⊆ (iterSys V).master := by
  induction N with
  | zero => exact subset_rfl
  | succ n ih => rw [NeighborhoodSystem.interUpTo_succ]; exact Set.inter_subset_left.trans ih

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/reconstruct_subset.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The finite intersection `⋂_{i<N} single i (fiber W i)` reconstructs `W` from below, once `N`
exceeds the cofinite-`Δ` bound of `W`. -/
theorem reconstruct_subset {W : Set (ℕ × α)} (_hW : (iterSys V).mem W) {N : ℕ}
    (hN : ∀ i, N ≤ i → fiber W i = V.master) :
    (iterSys V).interUpTo (fun i => single V i (fiber W i)) N ⊆ W := by
  rintro ⟨j, a⟩ ha
  by_cases h : j < N
  · have hsub := (iterSys V).interUpTo_subset (fun i => single V i (fiber W i)) h
    have hmem : (j, a) ∈ single V j (fiber W j) := hsub ha
    simpa [single] using hmem
  · have haM : a ∈ V.master := interUpTo_subset_master (fun i => single V i (fiber W i)) N ha
    have : a ∈ fiber W j := by rw [hN j (not_lt.mp h)]; exact haM
    exact this

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/single_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_inter {n : ℕ} (X X' : Set α) :
    single V n X ∩ single V n X' = single V n (X ∩ X') := by
  apply eq_of_fiber_eq
  intro i
  by_cases h : i = n
  · subst h; rw [fiber_inter, fiber_single_self, fiber_single_self, fiber_single_self]
  · rw [fiber_inter, fiber_single_ne h, fiber_single_ne h, fiber_single_ne h, Set.inter_self]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/single_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_master (n : ℕ) : single V n V.master = (iterSys V).master := by
  apply eq_of_fiber_eq
  intro i
  rw [fiber_iterSys_master]
  by_cases h : i = n
  · subst h; rw [fiber_single_self]
  · rw [fiber_single_ne h]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/single_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- `single V n X` is a `𝒟^∞`-neighbourhood whenever `X ∈ 𝒟`. -/
theorem single_mem {n : ℕ} {X : Set α} (hX : V.mem X) : (iterSys V).mem (single V n X) := by
  refine ⟨fun i => ?_, n + 1, fun i hi => ?_⟩
  · by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact V.master_mem
  · exact fiber_single_ne (by omega : i ≠ n) X

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/single_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_mono {n : ℕ} {X X' : Set α} (h : X ⊆ X') : single V n X ⊆ single V n X' := by
  intro p hp
  simp only [single, Set.mem_ofPred_eq] at hp ⊢
  by_cases hc : p.1 = n
  · rw [ite_eq_left hc] at hp ⊢; exact h hp
  · rw [ite_eq_right hc] at hp ⊢; exact hp

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/component.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The `n`-th component `xₙ ∈ |𝒟|` of a `𝒟^∞`-element `z` (Scott's coordinate at copy `n`). -/
def component (z : (iterSys V).Element) (n : ℕ) : V.Element where
  mem X := V.mem X ∧ z.mem (single V n X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [single_master]; exact z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz : z.mem (single V n (X ∩ X')) := by rw [← single_inter]; exact z.inter_mem hzX hzX'
    have hmem : V.mem (X ∩ X') := by
      have := (z.sub hz).1 n; rwa [fiber_single_self] at this
    exact ⟨hmem, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (single_mem hX') (single_mono hXX')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/mem_component.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem mem_component {z : (iterSys V).Element} {n : ℕ} {X : Set α} :
    (component z n).mem X ↔ V.mem X ∧ z.mem (single V n X) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/ofSeq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The `𝒟^∞`-element determined by an infinite sequence `⟨xₙ⟩` of `𝒟`-elements: the neighbourhoods
`W` whose every fiber lies in the corresponding `xᵢ`. -/
def ofSeq (seq : ℕ → V.Element) : (iterSys V).Element where
  mem W := (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i)
  sub h := h.1
  master_mem := ⟨(iterSys V).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (seq i).master_mem⟩
  inter_mem := by
    rintro W W' ⟨hW, hWf⟩ ⟨hW', hW'f⟩
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [fiber_inter]; exact (seq i).sub ((seq i).inter_mem (hWf i) (hW'f i))
    · obtain ⟨NW, hNW⟩ := hW.2
      obtain ⟨NW', hNW'⟩ := hW'.2
      refine ⟨max NW NW', fun i hi => ?_⟩
      rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
    · rw [fiber_inter]; exact (seq i).inter_mem (hWf i) (hW'f i)
  up_mem := by
    rintro W W' ⟨_, hWf⟩ hW' hWW'
    exact ⟨hW', fun i => (seq i).up_mem (hWf i) (hW'.1 i) (fiber_mono hWW' i)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/mem_ofSeq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem mem_ofSeq {seq : ℕ → V.Element} {W : Set (ℕ × α)} :
    (ofSeq seq).mem W ↔ (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/component_ofSeq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem component_ofSeq (seq : ℕ → V.Element) (n : ℕ) :
    component (ofSeq seq) n = seq n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨_, _, hfib⟩
    have := hfib n; rwa [fiber_single_self] at this
  · intro hX
    refine ⟨(seq n).sub hX, single_mem ((seq n).sub hX), fun i => ?_⟩
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact (seq i).master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/ofSeq_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem ofSeq_mono {seq seq' : ℕ → V.Element} (h : ∀ n, seq n ≤ seq' n) :
    ofSeq seq ≤ ofSeq seq' := by
  rintro W ⟨hW, hf⟩
  exact ⟨hW, fun i => h i _ (hf i)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/subset_single.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- Every `𝒟^∞`-neighbourhood is contained in the pinning of its own `i`-th fiber. -/
theorem subset_single {W : Set (ℕ × α)} (hW : (iterSys V).mem W) (i : ℕ) :
    W ⊆ single V i (fiber W i) := by
  rintro ⟨j, a⟩ ha
  simp only [single, Set.mem_ofPred_eq]
  by_cases h : j = i
  · rw [ite_eq_left h]; subst h; exact ha
  · rw [ite_eq_right h]; exact V.sub_master (hW.1 j) ha

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/ofSeq_component.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem ofSeq_component (z : (iterSys V).Element) :
    ofSeq (fun n => component z n) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hW, hfib⟩
    obtain ⟨N, hN⟩ := hW.2
    exact z.up_mem (z.mem_interUpTo _ (n := N) (fun i _ => (hfib i).2)) hW
      (reconstruct_subset hW hN)
  · intro hzW
    refine ⟨z.sub hzW, fun i => ?_⟩
    exact ⟨(z.sub hzW).1 i, z.up_mem hzW (single_mem ((z.sub hzW).1 i)) (subset_single (z.sub hzW) i)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/le_of_component_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- `z ⊑ z'` is detected component-wise. -/
theorem le_of_component_le {z z' : (iterSys V).Element}
    (h : ∀ n, component z n ≤ component z' n) : z ≤ z' := by
  have hmono := ofSeq_mono h
  rwa [ofSeq_component, ofSeq_component] at hmono

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/iterSeqEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The elements of `|𝒟^∞|` are in one-one,
order-preserving correspondence with infinite sequences `⟨xₙ⟩` of elements of `|𝒟|`. -/
def iterSeqEquiv (V : NeighborhoodSystem α) : (iterSys V).Element ≃o (∀ _ : ℕ, V.Element) where
  toFun z := fun n => component z n
  invFun seq := ofSeq seq
  left_inv z := ofSeq_component z
  right_inv seq := by funext n; exact component_ofSeq seq n
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h
      exact le_of_component_le (fun n => h n)
    · intro h n X hX
      exact ⟨hX.1, h (single V n X) hX.2⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/natShiftEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The shift order-isomorphism `(ℕ → E) ≃o E × (ℕ → E)`, `f ↦ (f 0, f ∘ succ)`. -/
def natShiftEquiv (E : Type*) [Preorder E] : (ℕ → E) ≃o E × (ℕ → E) where
  toFun f := (f 0, fun n => f (n + 1))
  invFun p := fun n => Nat.casesOn n p.1 (fun m => p.2 m)
  left_inv f := by funext n; cases n <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h0, hs⟩
      intro n
      cases n with
      | zero => exact h0
      | succ m => exact hs m
    · intro h
      exact ⟨h 0, fun m => h (m + 1)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/iterProdIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The isomorphism `|𝒟^∞| ≃o |𝒟 × 𝒟^∞|`, obtained from the
sequence correspondence and the shift. -/
def iterProdIso (V : NeighborhoodSystem α) :
    (iterSys V).Element ≃o (prod V (iterSys V)).Element :=
  (iterSeqEquiv V).trans <|
    (natShiftEquiv V.Element).trans <|
      (prodCongrOrderIso (OrderIso.refl V.Element) (iterSeqEquiv V).symm).trans
        (prodEquiv V (iterSys V)).symm

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/projN.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

open ApproximableMap

/-- The `n`-th coordinate projection `projN n : 𝒟^∞ → 𝒟`, `W (projN n) X ↔ fiber W n ⊆ X`. -/
def projN (V : NeighborhoodSystem α) (n : ℕ) : ApproximableMap (iterSys V) V where
  rel W X := (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, V.master_mem, by rw [fiber_iterSys_master]⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V.inter_mem hX hX' (hW.1 n) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, _, hsub⟩ hW₂W hXX₂ hW₂ hX₂
    exact ⟨hW₂, hX₂, (fiber_mono hW₂W n).trans (hsub.trans hXX₂)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}


theorem subset_of_fiber_subset {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i ⊆ fiber W' i) :
    W ⊆ W' := fun ⟨i, _⟩ ha => h i ha

variable (V : NeighborhoodSystem α)


variable {V}


open ApproximableMap


@[simp] theorem projN_rel {n : ℕ} {W : Set (ℕ × α)} {X : Set α} :
    (projN V n).rel W X ↔ (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X := Iff.rfl

@[simp] theorem toElementMap_projN (z : (iterSys V).Element) (n : ℕ) :
    (projN V n).toElementMap z = component z n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨W, hzW, hW, hX, hsub⟩
    refine ⟨hX, z.up_mem hzW (single_mem hX) ?_⟩
    refine subset_of_fiber_subset (fun i => ?_)
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hsub
    · rw [fiber_single_ne h]; exact V.sub_master (hW.1 i)
  · rintro ⟨hX, hz⟩
    exact ⟨single V n X, hz, single_mem hX, hX, by rw [fiber_single_self]⟩
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316/iter_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}


variable (V : NeighborhoodSystem α)


variable {V}


/-- **Exercise 3.16 (Scott 1981, PRG-19).** `𝒟^∞ ≅ 𝒟 × 𝒟^∞`. -/
theorem iter_isomorphic (V : NeighborhoodSystem α) : iterSys V ≅ᴰ prod V (iterSys V) :=
  ⟨iterProdIso V⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise316.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_316.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Isomorphic (Prod Nat α) (Sum α (Prod Nat α))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V)
    (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)) :=
  @DomainTheory.NeighbourhoodSystems.iter_isomorphic

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/prodMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.19(ii) (Scott 1981, PRG-19).** The product mapping `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`. -/
def prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (prod V₀ V₁) (prod V₀' V₁') :=
  paired (f.comp (proj₀ V₀ V₁)) (g.comp (proj₁ V₀ V₁))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/paired_unique.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (uniqueness):
any `k` with `p₀ ∘ k = h₀` and `p₁ ∘ k = h₁` equals the pairing `⟨h₀, h₁⟩`. Hence `prod` with
`proj₀`, `proj₁` is the categorical product of `𝒟₀` and `𝒟₁`. -/
theorem paired_unique (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
    (k : ApproximableMap V₂ (prod V₀ V₁)) (hk₀ : (proj₀ V₀ V₁).comp k = h₀)
    (hk₁ : (proj₁ V₀ V₁).comp k = h₁) : k = paired h₀ h₁ := by
  rw [← hk₀, ← hk₁, paired_proj]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/proj_paired.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (existence):
`p₀ ∘ ⟨h₀, h₁⟩ = h₀` and `p₁ ∘ ⟨h₀, h₁⟩ = h₁` (these are Proposition 3.4(i)). -/
theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/toElementMap_prodMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.19 (Scott 1981, PRG-19).** `(f × g)(w) = ⟨f(w₀), g(w₁)⟩` for every product element
`w` (so in particular `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, equation (i)). -/
theorem toElementMap_prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (w : (prod V₀ V₁).Element) :
    (prodMap f g).toElementMap w = pair (f.toElementMap w.fst) (g.toElementMap w.snd) := by
  rw [prodMap, toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/prodMap_comp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves composition:
`(f' ∘ f) × (g' ∘ g) = (f' × g') ∘ (f × g)`. -/
theorem prodMap_comp {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/prodMap_id.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319/toElementMap_prodMap_pair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.19(i) (Scott 1981, PRG-19).** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`. -/
theorem toElementMap_prodMap_pair (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (x : V₀.Element) (y : V₁.Element) :
    (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y) := by
  rw [toElementMap_prodMap, fst_pair, snd_pair]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise319.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_319.{u_1, u_2, u_4, u_5} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w)))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w))))
  @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap_pair @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** The *copairing* `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂`: a left copy
`0X` is routed through `a`, a right copy `1Y` through `b`, and the basepoint `Λ` to `⊥` (so `Λ`
relates only to `Δ₂`). -/
def copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) V₂ where
  rel W Z := (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
    (Z = V₂.master ∨
      (∃ X, W = inj₀ X ∧ a.rel X Z) ∨
      (∃ Y, W = inj₁ Y ∧ b.rel Y Z))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₂.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, _, hd⟩ ⟨_, _, hd'⟩
    have hmem : ∀ Z'' : Set γ,
        (Z'' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z'') ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z'')) →
        V₂.mem Z'' := by
      rintro Z'' (rfl | ⟨_, _, hf⟩ | ⟨_, _, hg⟩)
      · exact V₂.master_mem
      · exact a.rel_cod hf
      · exact b.rel_cod hg
    have key : Z ∩ Z' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X (Z ∩ Z')) ∨
        (∃ Y, W = inj₁ Y ∧ b.rel Y (Z ∩ Z')) := by
      rcases hd with rfl | ⟨X, hWX, hf⟩ | ⟨Y, hWY, hg⟩
      · rw [Set.inter_eq_right.mpr (V₂.sub_master (hmem _ hd'))]; exact hd'
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (a.rel_cod hf))]
          exact Or.inr (Or.inl ⟨X, hWX, hf⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX ▸ hWX')
          exact Or.inr (Or.inl ⟨X, hWX, a.inter_right hf hf'⟩)
        · exact absurd (hWX ▸ hWY' : (inj₀ X : Set _) = inj₁ Y')
            (fun h => not_inj₀_subset_inj₁ (h₀ X (a.rel_dom hf)) h.subset)
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (b.rel_cod hg))]
          exact Or.inr (Or.inr ⟨Y, hWY, hg⟩)
        · exact absurd (hWY ▸ hWX' : (inj₁ Y : Set _) = inj₀ X')
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (b.rel_dom hg)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY ▸ hWY')
          exact Or.inr (Or.inr ⟨Y, hWY, b.inter_right hg hg'⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, _, hd⟩ hW₂W hZZ' hW₂ hZ'
    refine ⟨hW₂, hZ', ?_⟩
    rcases hd with rfl | ⟨X, rfl, hf⟩ | ⟨Y, rfl, hg⟩
    · left; exact Set.Subset.antisymm (V₂.sub_master hZ') hZZ'
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      exact Or.inr (Or.inl ⟨X₂, rfl, a.mono hf (inj₀_subset_inj₀.mp hW₂W) hZZ' hX₂ hZ'⟩)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      exact Or.inr (Or.inr ⟨Y₂, rfl, b.mono hg (inj₁_subset_inj₁.mp hW₂W) hZZ' hY₂ hZ'⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copair_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

@[simp] theorem copair_rel {a : ApproximableMap V₀ V₂} {b : ApproximableMap V₁ V₂}
    {W : Set (Option (α ⊕ β))} {Z : Set γ} :
    (copair (h₀ := h₀) (h₁ := h₁) a b).rel W Z ↔ (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
      (Z = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z) ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copairProj.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- The canonical comparison `Hom(𝒟₀+𝒟₁, 𝒟₂) → Hom(𝒟₀,𝒟₂) × Hom(𝒟₁,𝒟₂)`, `h ↦ (h∘in₀, h∘in₁)`. -/
def copairProj (h : ApproximableMap (sum V₀ V₁ h₀ h₁) V₂) :
    ApproximableMap V₀ V₂ × ApproximableMap V₁ V₂ :=
  (h.comp inMap₀, h.comp inMap₁)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/prod_mem_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A product neighbourhood over non-empty factors is non-empty. -/
theorem prod_mem_nonempty (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (_hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (W : Set (α ⊕ β)) (hW : (prod V₀ V₁).mem W) : W.Nonempty := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW
  obtain ⟨a, ha⟩ := hn₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/distribMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.24(iii) (Scott 1981, PRG-19).** The canonical *distribution* approximable map
`(𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂) → 𝒟₀ × (𝒟₁ + 𝒟₂)`, `inᵢ⟨x, u⟩ ↦ ⟨x, inᵢ u⟩`. (This direction always exists;
the reverse map / isomorphism does not, since the left side has an element `⟨x, ⊥⟩` for each `x`.) -/
def distribMap (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (hn₂ : ∀ Z, V₂.mem Z → Z.Nonempty) :
    ApproximableMap
      (sum (prod V₀ V₁) (prod V₀ V₂) (prod_mem_nonempty hn₀ hn₁) (prod_mem_nonempty hn₀ hn₂))
      (prod V₀ (sum V₁ V₂ hn₁ hn₂)) :=
  copair
    (paired (proj₀ V₀ V₁) ((inMap₀ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₁)))
    (paired (proj₀ V₀ V₂) ((inMap₁ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₂)))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copair_comp_inMapu2080.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₀ = a`. -/
theorem copair_comp_inMap₀ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀ = a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact a.rel_master hX
    · exact a.mono hf (inj₀_subset_inj₀.mp (hWX' ▸ hinj)) subset_rfl hX hZ
    · exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY' ▸ hinj)).elim
  · intro hf
    exact ⟨inj₀ X, ⟨a.rel_dom hf, Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), a.rel_cod hf,
      Or.inr (Or.inl ⟨X, rfl, hf⟩)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copair_comp_inMapu2081.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₁ = b`. -/
theorem copair_comp_inMap₁ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁ = b := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact b.rel_master hY
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX' ▸ hinj)).elim
    · exact b.mono hg (inj₁_subset_inj₁.mp (hWY' ▸ hinj)) subset_rfl hY hZ
  · intro hg
    exact ⟨inj₁ Y, ⟨b.rel_dom hg, Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), b.rel_cod hg,
      Or.inr (Or.inr ⟨Y, rfl, hg⟩)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib/copairProj_copair.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `(𝒟₀→𝒟₂) × (𝒟₁→𝒟₂)` is a **retract** of
`(𝒟₀+𝒟₁) → 𝒟₂`: the copairing is a section of `h ↦ (h∘in₀, h∘in₁)`. (It is *not* an isomorphism: the
value of a map on the basepoint `Λ` is not recoverable from its restrictions to the two copies.) -/
theorem copairProj_copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    copairProj (h₀ := h₀) (h₁ := h₁) (copair a b) = (a, b) := by
  show ((copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀,
        (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁) = (a, b)
  rw [copair_comp_inMap₀, copair_comp_inMap₁]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Distrib.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324_distrib.{u_1, u_2, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
    (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) γ V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
        (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      b) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
    (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) γ V₁
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
        (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
        (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
      b)
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq
        (Prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.copairProj α β γ V₀ V₁ V₂ h₀ h₁
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b))
        (@Prod.mk (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) a b))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (b : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂),
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) γ V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₂
          (@DomainTheory.NeighbourhoodSystems.copair α β γ V₀ V₁ V₂ h₀ h₁ a b)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
        a)
    @DomainTheory.NeighbourhoodSystems.copairProj_copair @DomainTheory.NeighbourhoodSystems.copair_comp_inMap₀)
  @DomainTheory.NeighbourhoodSystems.copair_comp_inMap₁

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise326/TD.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- The truth domain `T` of Example 1.2 (neighbourhoods `{Δ, {0}, {1}}`). -/
abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/Tmem_eq_one.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- A `T`-neighbourhood contained in `{1}` is `{1}`. -/
theorem Tmem_eq_one {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.one) :
    C = Example12.one := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 0)) (by simp [Example12.one])
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])
  · rfl

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/Tmem_eq_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- A `T`-neighbourhood contained in `{0}` is `{0}` (the other two, `Δ` and `{1}`, are not). -/
theorem Tmem_eq_zero {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.zero) :
    C = Example12.zero := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 1)) (by simp [Example12.zero])
  · rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/condGuard.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- Scott's guard for `cond`, phrased with explicit equalities on the truth component
`C = inl⁻¹ W`. With `X = inl⁻¹ inr⁻¹ W` and `Y = inr⁻¹ inr⁻¹ W`:

* `C = {0}` (`true`):  `X ⊆ Z`;
* `C = {1}` (`false`): `Y ⊆ Z`;
* `C = Δ` (`⊥`):       `Δ_D ⊆ Z`. -/
def condGuard (V : NeighborhoodSystem α) (W : Set (Example12.Token ⊕ (α ⊕ α))) (Z : Set α) : Prop :=
  (Sum.inl ⁻¹' W = Example12.zero ∧ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.one ∧ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.master ∧ V.master ⊆ Z)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond_components.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- The three components `C, X, Y` of an input neighbourhood are themselves neighbourhoods. -/
theorem cond_components {W : Set (Example12.Token ⊕ (α ⊕ α))}
    (hW : (prod TD (prod V V)).mem W) :
    Example12.mem (Sum.inl ⁻¹' W) ∧
      V.mem (Sum.inl ⁻¹' (Sum.inr ⁻¹' W)) ∧ V.mem (Sum.inr ⁻¹' (Sum.inr ⁻¹' W)) := by
  obtain ⟨C, P, hC, hP, rfl⟩ := hW
  obtain ⟨X, Y, hX, hY, rfl⟩ := hP
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨hC, hX, hY⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/one_ne_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem one_ne_master : (Example12.one : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.one, Example12.master] at h0

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/zero_ne_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem zero_ne_master : (Example12.zero : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h1 := Set.ext_iff.mp h 1
  simp [Example12.zero, Example12.master] at h1

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/condGuard_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

theorem condGuard_master {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.master) : V.master ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨hC', _⟩ | ⟨_, h⟩
  · exact absurd (hC.symm.trans hC') zero_ne_master.symm
  · exact absurd (hC.symm.trans hC') one_ne_master.symm
  · exact h

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/zero_ne_one.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem zero_ne_one : (Example12.zero : Set Example12.Token) ≠ Example12.one := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.zero, Example12.one] at h0

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/condGuard_one.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

theorem condGuard_one {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.one) : Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨_, h⟩ | ⟨hC', _⟩
  · exact absurd (hC.symm.trans hC') zero_ne_one.symm
  · exact h
  · exact absurd (hC.symm.trans hC') one_ne_master

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/condGuard_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

theorem condGuard_zero {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.zero) : Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨_, h⟩ | ⟨hC', _⟩ | ⟨hC', _⟩
  · exact h
  · exact absurd (hC.symm.trans hC') zero_ne_one
  · exact absurd (hC.symm.trans hC') zero_ne_master

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The conditional operator `cond : T × D × D → D`. -/
def cond (V : NeighborhoodSystem α) : ApproximableMap (prod TD (prod V V)) V where
  rel W Z := (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨(prod TD (prod V V)).master_mem, V.master_mem, Or.inr (Or.inr ⟨?_, subset_rfl⟩)⟩
    show Sum.inl ⁻¹' (prod TD (prod V V)).master = Example12.master
    rw [prod_master, inl_preimage_prodNbhd]; rfl
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hg⟩ ⟨_, hZ', hg'⟩
    obtain ⟨_, hX, hY⟩ := cond_components V hW
    refine ⟨hW, ?_, ?_⟩
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact V.inter_mem hZ hZ' hX (Set.subset_inter hXZ (condGuard_zero V hg' hCz))
      · exact V.inter_mem hZ hZ' hY (Set.subset_inter hYZ (condGuard_one V hg' hCo))
      · exact V.inter_mem hZ hZ' V.master_mem (Set.subset_inter hmZ (condGuard_master V hg' hCm))
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact Or.inl ⟨hCz, Set.subset_inter hXZ (condGuard_zero V hg' hCz)⟩
      · exact Or.inr (Or.inl ⟨hCo, Set.subset_inter hYZ (condGuard_one V hg' hCo)⟩)
      · exact Or.inr (Or.inr ⟨hCm, Set.subset_inter hmZ (condGuard_master V hg' hCm)⟩)
  mono := by
    rintro W W₂ Z Z₂ ⟨hW, hZ, hg⟩ hW₂W hZZ₂ hW₂ hZ₂
    obtain ⟨hC₂, hX₂, hY₂⟩ := cond_components V hW₂
    refine ⟨hW₂, hZ₂, ?_⟩
    have hCsub : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hXsub : Sum.inl ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    have hYsub : Sum.inr ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
    · exact Or.inl ⟨Tmem_eq_zero hC₂ (hCsub.trans hCz.subset), (hXsub.trans hXZ).trans hZZ₂⟩
    · exact Or.inr (Or.inl ⟨Tmem_eq_one hC₂ (hCsub.trans hCo.subset),
        (hYsub.trans hYZ).trans hZZ₂⟩)
    · have hmZ₂ : V.master ⊆ Z₂ := hmZ.trans hZZ₂
      rcases (Example12.mem_iff (Sum.inl ⁻¹' W₂)).mp hC₂ with hC₂m | hC₂z | hC₂o
      · exact Or.inr (Or.inr ⟨hC₂m, hmZ₂⟩)
      · exact Or.inl ⟨hC₂z, (V.sub_master hX₂).trans hmZ₂⟩
      · exact Or.inr (Or.inl ⟨hC₂o, (V.sub_master hY₂).trans hmZ₂⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond_bot.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


/-- **Exercise 3.26(iii) (Scott 1981, PRG-19).** `cond(⊥, x, y) = ⊥`. -/
theorem cond_bot (x y : V.Element) :
    (cond V).toElementMap (pair Example23.botElt (pair x y)) = V.bot := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCbot, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    have hCm : C = Example12.master := hCbot
    rcases hg with ⟨hCz, _⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
    · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
    · rw [mem_bot, Set.Subset.antisymm (V.sub_master hZ) hmZ]
  · intro hbZ
    rw [mem_bot] at hbZ
    subst hbZ
    refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
      ⟨Example12.master, prodNbhd V.master V.master, rfl,
        ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
      V.master_mem, ?_⟩
    exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond_false.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


/-- **Exercise 3.26(ii) (Scott 1981, PRG-19).** `cond(false, x, y) = y`. -/
theorem cond_false (x y : V.Element) :
    (cond V).toElementMap (pair Example23.falseElt (pair x y)) = y := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCfalse, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, _⟩ | ⟨_, hYZ⟩ | ⟨_, hmZ⟩
    · rcases hCfalse with hCm | hCo
      · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
      · exact absurd (hCo.symm.trans hCz) zero_ne_one.symm
    · exact y.up_mem hYy hZ hYZ
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact y.master_mem
  · intro hyZ
    have hZ : V.mem Z := y.sub hyZ
    refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
      Or.inr rfl, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
    refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
    rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond_toElementMap_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


/-- The elementwise action of `cond`, computed at a paired argument `⟨t, ⟨x, y⟩⟩`: a neighbourhood
`Z` lies in `cond(t, x, y)` iff `t` selects `true` (`{0} ∈ t`) and `Z ∈ x`, or `t` selects `false`
(`{1} ∈ t`) and `Z ∈ y`, or `Z = Δ_D` (the always-present master). The three defining identities are
immediate corollaries. -/
theorem cond_toElementMap_mem (t : TD.Element) (x y : V.Element) {Z : Set α} :
    ((cond V).toElementMap (pair t (pair x y))).mem Z ↔
      (t.mem Example12.zero ∧ x.mem Z) ∨ (t.mem Example12.one ∧ y.mem Z) ∨ Z = V.master := by
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCt, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨_, hmZ⟩
    · exact Or.inl ⟨hCz ▸ hCt, x.up_mem hXx hZ hXZ⟩
    · exact Or.inr (Or.inl ⟨hCo ▸ hCt, y.up_mem hYy hZ hYZ⟩)
    · exact Or.inr (Or.inr (Set.Subset.antisymm (V.sub_master hZ) hmZ))
  · intro h
    rcases h with ⟨ht0, hxZ⟩ | ⟨ht1, hyZ⟩ | rfl
    · have hZ : V.mem Z := x.sub hxZ
      refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
        ht0, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
      refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
      rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
    · have hZ : V.mem Z := y.sub hyZ
      refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
        ht1, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
      refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
      rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]
    · refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
        ⟨Example12.master, prodNbhd V.master V.master, t.master_mem,
          ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
        V.master_mem, ?_⟩
      exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326/cond_true.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


/-- **Exercise 3.26(i) (Scott 1981, PRG-19).** `cond(true, x, y) = x`. -/
theorem cond_true (x y : V.Element) :
    (cond V).toElementMap (pair Example23.trueElt (pair x y)) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCtrue, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨_, hXZ⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact x.up_mem hXx hZ hXZ
    · rcases hCtrue with hCm | hCz
      · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
      · exact absurd (hCz.symm.trans hCo) zero_ne_one
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact x.master_mem
  · intro hxZ
    have hZ : V.mem Z := x.sub hxZ
    refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
      Or.inr rfl, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
    refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
    rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

set_option linter.unusedVariables false

theorem example_326.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y)
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
    @DomainTheory.NeighbourhoodSystems.Exercise326.cond_true @DomainTheory.NeighbourhoodSystems.Exercise326.cond_bot)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_false

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/Tmem_ge_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A `T`-neighbourhood containing `Δ` is `Δ`. -/
theorem Tmem_ge_master {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.master ⊆ C) : C = Example12.master :=
  Set.Subset.antisymm (Example12.neighborhoodSystem.sub_master hC) h

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/Tmem_ge_one.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A `T`-neighbourhood containing `{1}` is `{1}` or `Δ`. -/
theorem Tmem_ge_one {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.one ⊆ C) : C = Example12.one ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])
  · exact Or.inl rfl

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/Tmem_ge_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A `T`-neighbourhood containing `{0}` is `{0}` or `Δ`. -/
theorem Tmem_ge_zero {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.zero ⊆ C) : C = Example12.zero ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSumEmb.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- The embedding `T × D₀ × D₁ → T × S × S` (`S = D₀ + D₁`) that injects the two value slots into
the sum via `in₀` and `in₁`, leaving the truth slot fixed. -/
def condSumEmb (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (prod TD (prod (sum V₀ V₁ h₀ h₁) (sum V₀ V₁ h₀ h₁))) :=
  paired (proj₀ TD (prod V₀ V₁))
    (paired ((inMap₀ (h₀ := h₀) (h₁ := h₁)).comp ((proj₀ V₀ V₁).comp (proj₁ TD (prod V₀ V₁))))
      ((inMap₁ (h₀ := h₀) (h₁ := h₁)).comp ((proj₁ V₀ V₁).comp (proj₁ TD (prod V₀ V₁)))))

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSum.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The sum-valued conditional `T × D₀ × D₁ → D₀ + D₁`. -/
def condSum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (sum V₀ V₁ h₀ h₁) :=
  (cond (sum V₀ V₁ h₀ h₁)).comp (condSumEmb V₀ V₁ h₀ h₁)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/inter_in_oneset.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem inter_in_oneset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.one)
    (hc' : C' = Example12.master ∨ C' = Example12.one) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.one := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/inter_in_zeroset.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem inter_in_zeroset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.zero)
    (hc' : C' = Example12.master ∨ C' = Example12.zero) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.zero := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/whichGuard.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- Scott's guard for `which`: the truth output is `true` (`{0}`/`Δ`) on a left copy `0X`, `false`
(`{1}`/`Δ`) on a right copy `1Y`, and `⊥` (`Δ`) on the basepoint master. -/
def whichGuard (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (W : Set (Option (α ⊕ β))) (C : Set Example12.Token) : Prop :=
  ((∃ X, V₀.mem X ∧ W = inj₀ X) ∧ (C = Example12.master ∨ C = Example12.zero)) ∨
  ((∃ Y, V₁.mem Y ∧ W = inj₁ Y) ∧ (C = Example12.master ∨ C = Example12.one)) ∨
  (W = sumMaster V₀ V₁ ∧ C = Example12.master)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/whichGuard_left.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem whichGuard_left {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {X : Set α}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₀ X) (hX : X.Nonempty) :
    C = Example12.master ∨ C = Example12.zero := by
  rcases hg with ⟨_, hc⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨hWsm, _⟩
  · exact hc
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact not_inj₀_subset_inj₁ hX h.subset
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/whichGuard_masterC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem whichGuard_masterC {W : Set (Option (α ⊕ β))} {C : Set Example12.Token}
    (hg : whichGuard V₀ V₁ W C) (hW : W = sumMaster V₀ V₁) : C = Example12.master := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨_, hc⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)
  · exact hc

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/whichGuard_right.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem whichGuard_right {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {Y : Set β}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₁ Y) (hY : Y.Nonempty) :
    C = Example12.master ∨ C = Example12.one := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨_, hc⟩ | ⟨hWsm, _⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact not_inj₁_subset_inj₀ hY h.subset
  · exact hc
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/whichMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The discriminator `which : D₀ + D₁ → T`. -/
def whichMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) TD where
  rel W C := (sum V₀ V₁ h₀ h₁).mem W ∧ Example12.mem C ∧ whichGuard V₀ V₁ W C
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  inter_right := by
    rintro W C C' ⟨hW, _, hg⟩ ⟨_, _, hg'⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · have hor := inter_in_zeroset hc (whichGuard_left hg' rfl (h₀ X hX))
      refine ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), ?_, Or.inl ⟨⟨X, hX, rfl⟩, hor⟩⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_zero
    · have hor := inter_in_oneset hc (whichGuard_right hg' rfl (h₁ Y hY))
      refine ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), ?_, Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, hor⟩)⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_one
    · have hc' := whichGuard_masterC hg' rfl
      subst hc; subst hc'
      rw [Set.inter_self]
      exact ⟨Or.inl rfl, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  mono := by
    rintro W W₂ C C₂ ⟨hW, hC, hg⟩ hW₂W hCC₂ hW₂ hC₂
    refine ⟨hW₂, hC₂, ?_⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      refine Or.inl ⟨⟨X₂, hX₂, rfl⟩, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_zero hC₂ hCC₂)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      refine Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, ?_⟩)
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_one hC₂ hCC₂)
    · subst hc
      have hC₂m : C₂ = Example12.master := Tmem_ge_master hC₂ hCC₂
      rcases hW₂ with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hC₂m⟩)
      · exact Or.inl ⟨⟨X₂, hX₂, rfl⟩, Or.inl hC₂m⟩
      · exact Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, Or.inl hC₂m⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSumEmb_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


theorem condSumEmb_toElementMap (t : TD.Element) (x : V₀.Element) (y : V₁.Element) :
    (condSumEmb V₀ V₁ h₀ h₁).toElementMap (pair t (pair x y))
      = pair t (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
          ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)) := by
  simp only [condSumEmb, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSum_bot.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.26.** `condSum(⊥, x, y) = ⊥`. -/
theorem condSum_bot (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.botElt (pair x y)) = (sum V₀ V₁ h₀ h₁).bot := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_bot]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSum_false.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.26.** `condSum(false, x, y) = in₁(y)`. -/
theorem condSum_false (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.falseElt (pair x y))
      = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_false]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/condSum_true.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.26.** `condSum(true, x, y) = in₀(x)`. -/
theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/not_sum_mem_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- `∅` is never a sum-neighbourhood (every neighbourhood is non-empty). -/
theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/inMapu2080_outMapu2080_eq_of_left.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- On a "left" element (one reaching into the left copy), the round-trip `in₀ ∘ out₀` is the
identity. -/
theorem inMap₀_outMap₀_eq_of_left {x : (sum V₀ V₁ h₀ h₁).Element}
    (hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)) :
    (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨X₀, hX₀, hxX₀⟩ := hL
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, ⟨W, hxW, _, _, hLWX⟩, _, hSZ, hinjXZ⟩
    -- W ∩ inj₀ X₀ is a left copy inj₀ X₁ ⊆ Z, and lies in x
    have hxWX₀ : x.mem (W ∩ inj₀ X₀) := x.inter_mem hxW hxX₀
    obtain ⟨X₁, _, hX₁eq⟩ := mem_subset_inj₀ (x.sub hxWX₀) Set.inter_subset_right
    have hX₁X : X₁ ⊆ X := by
      have : leftPart V₀ (W ∩ inj₀ X₀) ⊆ X :=
        (leftPart_mono V₀ Set.inter_subset_left).trans hLWX
      rwa [hX₁eq, leftPart_inj₀] at this
    have : (W ∩ inj₀ X₀) ⊆ Z :=
      hX₁eq ▸ (inj₀_subset_inj₀.mpr hX₁X).trans hinjXZ
    exact x.up_mem hxWX₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · -- Z = sumMaster
      exact ⟨V₀.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩, V₀.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
    · -- Z = inj₀ X'
      exact ⟨X', ⟨inj₀ X', hxZ, Or.inr (Or.inl ⟨X', hX', rfl⟩), hX', (leftPart_inj₀ V₀ X').subset⟩,
        hX', Or.inr (Or.inl ⟨X', hX', rfl⟩), subset_rfl⟩
    · -- Z = inj₁ Y' is impossible for a left element
      have := x.inter_mem hxX₀ hxZ
      rw [inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/inMapu2081_outMapu2081_eq_of_right.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- On a "right" element, the round-trip `in₁ ∘ out₁` is the identity. -/
theorem inMap₁_outMap₁_eq_of_right {x : (sum V₀ V₁ h₀ h₁).Element}
    (hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) :
    (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨Y₀, hY₀, hxY₀⟩ := hR
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, ⟨W, hxW, _, _, hRWY⟩, _, hSZ, hinjYZ⟩
    have hxWY₀ : x.mem (W ∩ inj₁ Y₀) := x.inter_mem hxW hxY₀
    obtain ⟨Y₁, _, hY₁eq⟩ := mem_subset_inj₁ (x.sub hxWY₀) Set.inter_subset_right
    have hY₁Y : Y₁ ⊆ Y := by
      have : rightPart V₁ (W ∩ inj₁ Y₀) ⊆ Y :=
        (rightPart_mono V₁ Set.inter_subset_left).trans hRWY
      rwa [hY₁eq, rightPart_inj₁] at this
    have : (W ∩ inj₁ Y₀) ⊆ Z :=
      hY₁eq ▸ (inj₁_subset_inj₁.mpr hY₁Y).trans hinjYZ
    exact x.up_mem hxWY₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact ⟨V₁.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩, V₁.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
    · have := x.inter_mem hxY₀ hxZ
      rw [Set.inter_comm, inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty
    · exact ⟨Y', ⟨inj₁ Y', hxZ, Or.inr (Or.inr ⟨Y', hY', rfl⟩), hY', (rightPart_inj₁ V₁ Y').subset⟩,
        hY', Or.inr (Or.inr ⟨Y', hY', rfl⟩), subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/sum_element_trichotomy.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- Trichotomy for a sum-element: it reaches the left copy, or the right copy, or is `⊥`. -/
theorem sum_element_trichotomy (x : (sum V₀ V₁ h₀ h₁).Element) :
    (∃ X, V₀.mem X ∧ x.mem (inj₀ X)) ∨ (∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) ∨
      (∀ W, x.mem W → W = (sum V₀ V₁ h₀ h₁).master) := by
  by_cases hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)
  · exact Or.inl hL
  by_cases hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)
  · exact Or.inr (Or.inl hR)
  refine Or.inr (Or.inr ?_)
  intro W hxW
  rcases x.sub hxW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rfl
  · exact absurd ⟨X, hX, hxW⟩ hL
  · exact absurd ⟨Y, hY, hxW⟩ hR

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/which_mem_one.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- `which(x)` selects `false` (`{1} ∈ which x`) exactly when `x` reaches into the right copy. -/
theorem which_mem_one {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.one
      ↔ ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨_, hc⟩ | ⟨⟨Y, hY, rfl⟩, _⟩ | ⟨_, hc⟩
    · rcases hc with h | h
      · exact absurd h one_ne_master
      · exact absurd h zero_ne_one.symm
    · exact ⟨Y, hY, hWx⟩
    · exact absurd hc one_ne_master
  · rintro ⟨Y, hY, hWx⟩
    exact ⟨inj₁ Y, hWx, Or.inr (Or.inr ⟨Y, hY, rfl⟩), Example12.mem_one,
      Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, Or.inr rfl⟩)⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/which_mem_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- `which(x)` selects `true` (`{0} ∈ which x`) exactly when `x` reaches into the left copy. -/
theorem which_mem_zero {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.zero
      ↔ ∃ X, V₀.mem X ∧ x.mem (inj₀ X) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · exact ⟨X, hX, hWx⟩
    · rcases hc with h | h
      · exact absurd h zero_ne_master
      · exact absurd h zero_ne_one
    · exact absurd hc zero_ne_master
  · rintro ⟨X, hX, hWx⟩
    exact ⟨inj₀ X, hWx, Or.inr (Or.inl ⟨X, hX, rfl⟩), Example12.mem_zero,
      Or.inl ⟨⟨X, hX, rfl⟩, Or.inr rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum/cond_which.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.26 (Scott 1981, PRG-19).** Scott's identity for the discriminator:
`cond(which x, in₀(out₀ x), in₁(out₁ x)) = x` for every `x ∈ |D₀ + D₁|`. -/
theorem cond_which (x : (sum V₀ V₁ h₀ h₁).Element) :
    (cond (sum V₀ V₁ h₀ h₁)).toElementMap
        (pair ((whichMap V₀ V₁ h₀ h₁).toElementMap x)
          (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x))
                ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x)))) = x := by
  apply Element.ext
  intro Z
  rw [cond_toElementMap_mem, which_mem_zero, which_mem_one]
  constructor
  · rintro (⟨hL, ha⟩ | ⟨hR, hb⟩ | rfl)
    · rwa [inMap₀_outMap₀_eq_of_left hL] at ha
    · rwa [inMap₁_outMap₁_eq_of_right hR] at hb
    · exact x.master_mem
  · intro hxZ
    rcases sum_element_trichotomy x with hL | hR | hN
    · exact Or.inl ⟨hL, by rw [inMap₀_outMap₀_eq_of_left hL]; exact hxZ⟩
    · exact Or.inr (Or.inl ⟨hR, by rw [inMap₁_outMap₁_eq_of_right hR]; exact hxZ⟩)
    · exact Or.inr (Or.inr (hN Z hxZ))

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- Exercise326Sum.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise326

set_option linter.unusedVariables false

theorem example_326_sum.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x)
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y))
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_bot
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_false)
    @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_true)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_which

end DomainTheory.NeighbourhoodSystems.Exercise326
end

section
-- FunctionSpace/BasicInst3.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Approximable maps are ordered by inclusion of their relations (Scott's approximation order on
`|𝒟₀ → 𝒟₁|`). Antisymmetry is `ApproximableMap.ext`. -/
instance : PartialOrder (ApproximableMap V₀ V₁) where
  le f g := ∀ X Y, f.rel X Y → g.rel X Y
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 X Y h := h2 X Y (h1 X Y h)
  le_antisymm f g h1 h2 := ApproximableMap.ext fun X Y => ⟨h1 X Y, h2 X Y⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/step.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's step set `[X, Y] = {f ∣ X f Y}`. -/
def step (X : Set α) (Y : Set β) : Set (ApproximableMap V₀ V₁) := {f | f.rel X Y}

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mem_step.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_step {X : Set α} {Y : Set β} {f : ApproximableMap V₀ V₁} :
    f ∈ step X Y ↔ f.rel X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A finite intersection of step sets, indexed by a list of `(X, Y)` pairs. -/
def stepFun (L : List (Set α × Set β)) : Set (ApproximableMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.rel p.1 p.2}

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mem_stepFun.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_stepFun {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} :
    f ∈ stepFun L ↔ ∀ p ∈ L, f.rel p.1 p.2 := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_nil.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem stepFun_nil : (stepFun [] : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simp

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_append.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem stepFun_append (L L' : List (Set α × Set β)) :
    (stepFun (L ++ L') : Set (ApproximableMap V₀ V₁)) = stepFun L ∩ stepFun L' := by
  ext f
  simp only [mem_stepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_cons.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem stepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (stepFun (p :: L) : Set (ApproximableMap V₀ V₁)) = step p.1 p.2 ∩ stepFun L := by
  ext f
  simp only [mem_stepFun, List.mem_cons, Set.mem_inter_iff, mem_step]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_singleton.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem stepFun_singleton (X : Set α) (Y : Set β) :
    (stepFun [(X, Y)] : Set (ApproximableMap V₀ V₁)) = step X Y := by
  rw [stepFun_cons, stepFun_nil, Set.inter_univ]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/step_master_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem step_master_eq : (step V₀.master V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.master_rel

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpace.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Definition 3.8 (Scott 1981, PRG-19).** The *function space* `(𝒟₀ → 𝒟₁)`: tokens are
approximable maps, neighbourhoods are non-empty finite intersections of step sets. -/
def funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (ApproximableMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, stepFun_nil.symm⟩, ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpace_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem funSpace_master : (funSpace V₀ V₁).master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpace_mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem funSpace_mem_iff {W : Set (ApproximableMap V₀ V₁)} :
    (funSpace V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
        ∧ W.Nonempty := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/step_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `[X, Y] ∩ [X, Y'] = [X, Y ∩ Y']` (intersectivity in the output). -/
theorem step_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (step X Y ∩ step X Y' : Set (ApproximableMap V₀ V₁)) = step X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_step]
  constructor
  · rintro ⟨h, h'⟩; exact f.inter_right h h'
  · intro h
    exact ⟨f.mono h subset_rfl Set.inter_subset_left (f.rel_dom h) hY,
           f.mono h subset_rfl Set.inter_subset_right (f.rel_dom h) hY'⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/step_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A step neighbourhood `[X, Y]` is a neighbourhood of the function space (non-empty: it contains
the constant map `constMap V₀ (↑Y)`). -/
theorem step_mem {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (funSpace V₀ V₁).mem (step X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (stepFun_singleton X Y).symm⟩,
    ⟨constMap V₀ (V₁.principal hY), ?_⟩⟩
  · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hX, hY⟩
  · show (constMap V₀ (V₁.principal hY)).rel X Y
    exact ⟨hX, hY, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mem_stepFun_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The "generation" lemma: a filter contains the intersection `stepFun L` iff it contains each
step `[Xᵢ, Yᵢ]`. (The step sets `[X, Y] ∈ φ` generate the filter `φ`.) -/
theorem mem_stepFun_iff (φ : (funSpace V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (stepFun L) ↔ ∀ p ∈ L, φ.mem (step p.1 p.2) := by
  induction L with
  | nil => simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hstep : φ.mem (step p.1 p.2) :=
        φ.up_mem hmem (step_mem hp.1 hp.2) Set.inter_subset_left
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (stepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/step_subset.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `X' ⊆ X` and `Y ⊆ Y'` imply `[X, Y] ⊆ [X', Y']`. -/
theorem step_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (step X Y : Set (ApproximableMap V₀ V₁)) ⊆ step X' Y' := by
  intro f hf
  exact f.mono hf hX'X hYY' hX' hY'

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toApproxMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The relation `X φ̂ Y ↔ [X, Y] ∈ φ` of a filter `φ`.
Intersectivity is the payoff of positivity (`[X,Y]∩[X,Y'] = [X,Y∩Y']` is non-empty, so `Y∩Y' ∈ 𝒟₁`). -/
def toApproxMap (φ : (funSpace V₀ V₁).Element) : ApproximableMap V₀ V₁ where
  rel X Y := φ.mem (step X Y)
  rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_dom hf
  rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_cod hf
  master_rel := by show φ.mem (step V₀.master V₁.master); rw [step_master_eq]; exact φ.master_mem
  inter_right := by
    intro X Y Y' h h'
    obtain ⟨f, hf⟩ := (φ.sub h).2
    obtain ⟨f', hf'⟩ := (φ.sub h').2
    have hY : V₁.mem Y := f.rel_cod hf
    have hY' : V₁.mem Y' := f'.rel_cod hf'
    show φ.mem (step X (Y ∩ Y'))
    rw [← step_inter_right hY hY']
    exact φ.inter_mem h h'
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY'
    show φ.mem (step X' Y')
    exact φ.up_mem h (step_mem hX' hY') (step_subset hX' hY' hX'X hYY')

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toApproxMap_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem toApproxMap_rel {φ : (funSpace V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toApproxMap φ).rel X Y ↔ φ.mem (step X Y) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toFilter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The filter `f̂ = {F ∣ f ∈ F}` of an approximable map. -/
def toFilter (f : ApproximableMap V₀ V₁) : (funSpace V₀ V₁).Element where
  mem W := (funSpace V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(funSpace V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
    refine ⟨⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, ⟨f, ?_⟩⟩, ?_⟩
    · intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hL p h
      · exact hL' p h
    · exact Set.mem_inter hfW hfW'
    · exact Set.mem_inter hfW hfW'
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mem_toFilter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_toFilter {f : ApproximableMap V₀ V₁} {W : Set (ApproximableMap V₀ V₁)} :
    (toFilter f).mem W ↔ (funSpace V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpaceEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The function space is *complete*: every filter is fixed
by a unique approximable mapping, inclusion-preservingly. -/
def funSpaceEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁ where
  toFun := toApproxMap
  invFun := toFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_stepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_stepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨step_mem (f.rel_dom hf) (f.rel_cod hf), hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_stepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_stepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpaceEquiv_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem funSpaceEquiv_apply (φ : (funSpace V₀ V₁).Element) :
    funSpaceEquiv V₀ V₁ φ = toApproxMap φ := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpaceEquiv_symm_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem funSpaceEquiv_symm_apply (f : ApproximableMap V₀ V₁) :
    (funSpaceEquiv V₀ V₁).symm f = toFilter f := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpace_mem_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Intersection of two function-space neighbourhoods, when non-empty, is again one. -/
theorem funSpace_mem_inter {W W' : Set (ApproximableMap V₀ V₁)}
    (hW : (funSpace V₀ V₁).mem W) (hW' : (funSpace V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (funSpace V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's intersection `⋂ {Yᵢ ∣ X ⊆ Xᵢ}` of the outputs whose input is coarser than `X`, taken
inside the master neighbourhood `Δ₁` (so the empty intersection is `Δ₁`, per the convention 1.1a).
Indexed by the list `L` of `(Xᵢ, Yᵢ)` pairs. -/
def interYs (m : Set β) : List (Set α × Set β) → Set α → Set β
  | [], _ => m
  | p :: L, X => {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs_nil.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem interYs_nil (m : Set β) (X : Set α) : interYs m [] X = m := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs_cons.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem interYs_cons (m : Set β) (p : Set α × Set β) (L : List (Set α × Set β)) (X : Set α) :
    interYs m (p :: L) X = {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mem_interYs.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Membership in `interYs`: `z ∈ ⋂{Yᵢ ∣ X ⊆ Xᵢ}` iff `z ∈ Δ₁` and `z ∈ Yᵢ` for every `i` with
`X ⊆ Xᵢ`. -/
theorem mem_interYs {m : Set β} {L : List (Set α × Set β)} {X : Set α} {z : β} :
    z ∈ interYs m L X ↔ z ∈ m ∧ ∀ p ∈ L, X ⊆ p.1 → z ∈ p.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [interYs_cons]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hp, hm, hL⟩
      refine ⟨hm, ?_⟩
      rintro q (rfl | hq) hXq
      · exact hp hXq
      · exact hL q hq hXq
    · rintro ⟨hm, hall⟩
      exact ⟨fun hXp => hall p (Or.inl rfl) hXp, hm,
        fun q hq hXq => hall q (Or.inr hq) hXq⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs_antitone.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `interYs` is antitone in the input `X`: a sharper input intersects over more outputs. -/
theorem interYs_antitone {m : Set β} {L : List (Set α × Set β)} {X X' : Set α} (h : X' ⊆ X) :
    interYs m L X' ⊆ interYs m L X := by
  intro z hz
  rw [mem_interYs] at hz ⊢
  exact ⟨hz.1, fun p hp hXp => hz.2 p hp (h.trans hXp)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs_subset_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `interYs` is contained in the master neighbourhood. -/
theorem interYs_subset_master {m : Set β} {L : List (Set α × Set β)} {X : Set α} :
    interYs m L X ⊆ m := fun _ hz => (mem_interYs.mp hz).1

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/leastMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Proposition 3.9(ii) (Scott 1981, PRG-19).** The *least* approximable mapping `f₀` belonging to
the neighbourhood `⋂ [Xᵢ, Yᵢ]`, defined by `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. Well-definedness uses
Scott's condition (i) in the operational form `hcons`: for every neighbourhood `X`, the outputs
`{Yᵢ ∣ X ⊆ Xᵢ}` (consistent in `𝒟₁`, witnessed by `X` being a common lower bound of their inputs)
have their intersection again a neighbourhood. -/
def leastMap (L : List (Set α × Set β)) (_hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, V₁.master_mem, interYs_subset_master⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, V₁.inter_mem hY hY' (hcons hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (interYs_antitone hX'X).trans (hsub.trans hYY')⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/leastMap_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem leastMap_rel {L : List (Set α × Set β)}
    {hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2}
    {hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)} {X : Set α} {Y : Set β} :
    (leastMap L hL hcons).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/MapsBounded.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A set `F` of approximable maps is *bounded* when it has an upper bound in the map order. -/
def MapsBounded (F : Set (ApproximableMap V₀ V₁)) : Prop := ∃ h, ∀ f ∈ F, f ≤ h

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/PointwiseBounded.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `F` is *pointwise bounded* when `{f(x) ∣ f ∈ F}` is bounded in `|𝒟₁|` for every `x`. -/
def PointwiseBounded (F : Set (ApproximableMap V₀ V₁)) : Prop :=
  ∀ x : V₀.Element, V₁.Bounded (Set.image (fun f => f.toElementMap x) F)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/eval.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.11 (Scott 1981, PRG-19).** The two-variable evaluation map
`eval : (𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`, `F, X eval Y ↔ X f Y for all f ∈ F`. -/
def eval (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap₂ (funSpace V₁ V₂) V₁ V₂ where
  rel F X Y := (funSpace V₁ V₂).mem F ∧ V₁.mem X ∧ V₂.mem Y ∧ ∀ f ∈ F, f.rel X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨(funSpace V₁ V₂).master_mem, V₁.master_mem, V₂.master_mem,
    fun f _ => f.master_rel⟩
  inter_right := by
    rintro F X Y Y' ⟨hF, hX, hY, hrel⟩ ⟨_, _, hY', hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hF).2
    refine ⟨hF, hX, ?_, fun g hg => g.inter_right (hrel g hg) (hrel' g hg)⟩
    exact f.rel_cod (f.inter_right (hrel f hf) (hrel' f hf))
  mono := by
    rintro F F' X X' Y Y' ⟨hF, hX, hY, hrel⟩ hF'F hX'X hYY' hF' hX' hY'
    exact ⟨hF', hX', hY', fun f hf => f.mono (hrel f (hF'F hf)) hX'X hYY' hX' hY'⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/evalMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.11 (Scott 1981, PRG-19).** Evaluation as a single approximable map out of the
product `(𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`. -/
def evalMap (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) V₁) V₂ := ofMap₂ (eval V₁ V₂)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/gSection.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The `X`-section of a two-variable map `g : 𝒟₀ × 𝒟₁ → 𝒟₂`: the map `𝒟₁ → 𝒟₂` with
`Y (gSection g X) Z ↔ X ∪ Y g Z`. -/
def gSection (g : ApproximableMap (prod V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ where
  rel Y Z := g.rel (prodNbhd X Y) Z
  rel_dom h := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  rel_cod h := g.rel_cod h
  master_rel := g.rel_master (prod_mem_prodNbhd hX V₁.master_mem)
  inter_right h h' := g.inter_right h h'
  mono := by
    intro Y Y' Z Z' h hY'Y hZZ' hY' hZ'
    exact g.mono h (prodNbhd_subset_iff.mpr ⟨subset_rfl, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX hY') hZ'

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/gSection_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

@[simp] theorem gSection_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} : (gSection g hX).rel Y Z ↔ g.rel (prodNbhd X Y) Z := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/gSection_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

theorem gSection_le {g : ApproximableMap (prod V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) : gSection g hX ≤ gSection g hX' := by
  intro Y Z h
  have hY := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  exact g.mono h (prodNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩) subset_rfl
    (prod_mem_prodNbhd hX' hY) (g.rel_cod h)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mapsBounded_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem mapsBounded_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    V₁.Bounded (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) :=
  hF (V₀.principal hX)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_up_closed.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Step neighbourhoods are *up-closed* under the map order: if `f ∈ stepFun L` and `f ⊑ f'`, then
`f' ∈ stepFun L`. -/
theorem stepFun_up_closed {L : List (Set α × Set β)} {f f' : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) (hff' : f ≤ f') : f' ∈ stepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/funSpace_mem_up_closed.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A function-space neighbourhood is up-closed under the map order. -/
theorem funSpace_mem_up_closed {W : Set (ApproximableMap V₀ V₁)} (hW : (funSpace V₀ V₁).mem W)
    {f f' : ApproximableMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact stepFun_up_closed hf hff'

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/curry.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry(g) : 𝒟₀ → (𝒟₁ → 𝒟₂)`, where
`X curry(g) W ↔ (the X-section of g) ∈ W` (for `W = [Y, Z]` this is `X ∪ Y g Z`). -/
def curry (g : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap V₀ (funSpace V₁ V₂) where
  rel X W := ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hW, _⟩ => hW
  master_rel := ⟨V₀.master_mem, (funSpace V₁ V₂).master_mem, Set.mem_univ _⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hmem⟩ ⟨_, hW', hmem'⟩
    exact ⟨hX, funSpace_mem_inter hW hW' ⟨gSection g hX, hmem, hmem'⟩,
      Set.mem_inter hmem hmem'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hmem⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', funSpace_mem_up_closed hW' (hWW' hmem) (gSection_le hX hX' hX'X)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/curry_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

@[simp] theorem curry_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α}
    {W : Set (ApproximableMap V₁ V₂)} :
    (curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/prod_mem_inl.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

theorem prod_mem_inl {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₀.mem (Sum.inl ⁻¹' W) := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW; rwa [inl_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/prod_mem_inr.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

theorem prod_mem_inr {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₁.mem (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, hY, rfl⟩ := hW; rwa [inr_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/rel_stepFun_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The relational generation lemma for maps `h : 𝒟₀ → (𝒟₁ → 𝒟₂)`: `X h (⋂ᵢ [Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_stepFun_iff (h : ApproximableMap V₀ (funSpace V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (stepFun L) ↔ ∀ p ∈ L, h.rel X (step p.1 p.2) := by
  induction L with
  | nil =>
    simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (funSpace V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (h.rel_cod hmem).2
      have hstep : h.rel X (step p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (step_mem hp.1 hp.2)
      have htail : h.rel X (stepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/supOnPrincipal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The sup of `{f(↑X) ∣ f ∈ F}` on principal inputs, used to build `sSupMaps`. -/
def supOnPrincipal (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X : Set α) (hX : V₀.mem X) : V₁.Element :=
  V₁.sSup (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) (mapsBounded_principal hF hX)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/supOnPrincipal_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem supOnPrincipal_mono (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    supOnPrincipal F hF X hX ≤ supOnPrincipal F hF X' hX' :=
  V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
    obtain ⟨f, hf, rfl⟩ := hs
    exact (toElementMap_mono f ((V₀.principal_le_iff hX hX').mpr hX'X)).trans
      (V₁.le_sSup _ (mapsBounded_principal hF hX') ⟨f, hf, rfl⟩)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/sSupMaps.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** The least upper bound of a pointwise-bounded set
`F`, defined on principal inputs by `supOnPrincipal` and extended via Exercise 2.8 (`ofMono`). -/
def sSupMaps (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) : ApproximableMap V₀ V₁ :=
  ofMono (fun X hX => supOnPrincipal F hF X hX) (supOnPrincipal_mono F hF)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/uncurry.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** Uncurrying `h : 𝒟₀ → (𝒟₁ → 𝒟₂)` to `𝒟₀ × 𝒟₁ → 𝒟₂`:
`X ∪ Y (uncurry h) Z ↔ X h [Y, Z]`. -/
def uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z)
  rel_dom h' := h'.1
  rel_cod := by
    rintro W Z ⟨_, hrel⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    exact f.rel_cod hf
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    rw [show (prod V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
      inl_preimage_prodNbhd, inr_preimage_prodNbhd, step_master_eq]
    exact h.master_rel
  inter_right := by
    rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    obtain ⟨f', hf'⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel')).2
    refine ⟨hW, ?_⟩
    rw [← step_inter_right (f.rel_cod hf) (f'.rel_cod hf')]
    exact h.inter_right hrel hrel'
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl ⊢
    rw [inr_preimage_prodNbhd] at hinr ⊢
    refine ⟨prod_mem_prodNbhd hA hB, ?_⟩
    exact h.mono hrel hinl (step_subset hB hZ' hinr hZZ') hA (step_mem hB hZ')

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/uncurry_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

@[simp] theorem uncurry_rel {h : ApproximableMap V₀ (funSpace V₁ V₂)}
    {W : Set (α ⊕ β)} {Z : Set γ} :
    (uncurry h).rel W Z ↔
      (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/curry_uncurry.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry (uncurry h) = h`. -/
theorem curry_uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : curry (uncurry h) = h := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨hX, hW, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    refine (rel_stepFun_iff h hX hL).mpr (fun p hp => ?_)
    have := hmem p hp
    -- `gSection (uncurry h) hX ∈ step p.1 p.2` means `(uncurry h).rel (prodNbhd X p.1) p.2`
    have hrel : (uncurry h).rel (prodNbhd X p.1) p.2 := this
    obtain ⟨_, hrel'⟩ := hrel
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel'
    exact hrel'
  · intro hrel
    have hX : V₀.mem X := h.rel_dom hrel
    have hW : (funSpace V₁ V₂).mem W := h.rel_cod hrel
    refine ⟨hX, hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    intro p hp
    show (uncurry h).rel (prodNbhd X p.1) p.2
    refine ⟨prod_mem_prodNbhd hX (hL p hp).1, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact (rel_stepFun_iff h hX hL).mp hrel p hp

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/uncurry_curry.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `uncurry (curry g) = g`. -/
theorem uncurry_curry (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g := by
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, _, _, hmem⟩
    rw [prodNbhd_preimage hW]; exact hmem
  · intro hrel
    have hW := g.rel_dom hrel
    refine ⟨hW, prod_mem_inl hW, step_mem (prod_mem_inr hW) (g.rel_cod hrel), ?_⟩
    show g.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z
    rwa [← prodNbhd_preimage hW]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/curryEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry` is an order-isomorphism between
`|𝒟₀ × 𝒟₁ → 𝒟₂|` and `|𝒟₀ → (𝒟₁ → 𝒟₂)|`. -/
def curryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (curry g).rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := by
        have hu : (uncurry (curry g)).rel W Z := by rw [uncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (uncurry (curry g')).rel W Z := ⟨g.rel_dom hrel, h2⟩
      rw [uncurry_curry] at hu'
      exact hu'
    · intro hg X W hrel
      obtain ⟨hX, hW, hmem⟩ := hrel
      refine ⟨hX, hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
      intro p hp
      have hgrel : g.rel (prodNbhd X p.1) p.2 := hmem p hp
      exact hg _ _ hgrel

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/ApproximableMapu2ele_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem ApproximableMap.le_iff {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ X Y, f.rel X Y → g.rel X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/interYs_subset_of_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `interYs` contains `Yⱼ` whenever `Xⱼ ⊆ X`-indexed: in particular `interYs m L Xⱼ ⊆ Yⱼ` for
`(Xⱼ, Yⱼ) ∈ L`. -/
theorem interYs_subset_of_mem {m : Set β} {L : List (Set α × Set β)} {p : Set α × Set β}
    (hp : p ∈ L) : interYs m L p.1 ⊆ p.2 :=
  fun _ hz => (mem_interYs.mp hz).2 p hp subset_rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/le_iff_toElementMap_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 3.13(i) (Scott 1981, PRG-19).** `f ⊑ g ↔ ∀ x, f(x) ⊑ g(x)`. -/
theorem le_iff_toElementMap_le {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ x, f.toElementMap x ≤ g.toElementMap x := by
  constructor
  · intro h x Y ⟨X, hXx, hrel⟩
    exact ⟨X, hXx, h X Y hrel⟩
  · intro h X Y hrel
    have hX : V₀.mem X := f.rel_dom hrel
    rw [f.rel_iff_mem_principal hX] at hrel
    rw [g.rel_iff_mem_principal hX]
    exact h (V₀.principal hX) Y hrel

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/le_sSupMaps.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem le_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ F) : f ≤ sSupMaps F hF := by
  intro X Y hrel
  have hX : V₀.mem X := f.rel_dom hrel
  have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
  exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hF hX) ⟨f, hf, rfl⟩) Y hmem⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/leastMap_mem_stepFun.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mapsBounded_iff_pointwiseBounded.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 3.13(ii) (Scott 1981, PRG-19).** `F` is bounded in `|𝒟₀ → 𝒟₁|` iff `{f(x) ∣ f ∈ F}` is
bounded in `|𝒟₁|` for each `x ∈ |𝒟₀|`. The forward direction is `le_iff_toElementMap_le` (3.13(i))
applied pointwise; the backward direction builds the bound `sSupMaps F`. -/
theorem mapsBounded_iff_pointwiseBounded {F : Set (ApproximableMap V₀ V₁)} :
    MapsBounded F ↔ PointwiseBounded F := by
  constructor
  · intro ⟨h, hh⟩ x
    refine ⟨h.toElementMap x, fun z hz => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hz
    exact (le_iff_toElementMap_le.mp (hh f hf)) x
  · intro hpb
    refine ⟨sSupMaps F hpb, fun f hf X Y hrel => ?_⟩
    have hX : V₀.mem X := f.rel_dom hrel
    have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
    exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hpb hX) ⟨f, hf, rfl⟩) Y hmem⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/rel_interYs.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The relation `X f Y` holds for `f` in the neighbourhood `stepFun L` at the master output, and
more importantly `f` relates `X` to the whole intersection `interYs Δ₁ L X` (finite intersectivity
over the relevant outputs). The case split deciding `X ⊆ Xᵢ` is a documented classical step. -/
theorem rel_interYs {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} (hf : f ∈ stepFun L)
    {X : Set α} (hX : V₀.mem X) : f.rel X (interYs V₁.master L X) := by
  induction L with
  | nil =>
    rw [interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem
  | cons p L ih =>
    have hftail : f ∈ stepFun L := fun q hq => hf q (List.mem_cons.mpr (Or.inr hq))
    have htail := ih hftail
    by_cases hXp : X ⊆ p.1
    · have hp : f.rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel X p.2 := f.mono hp hXp subset_rfl hX (f.rel_cod hp)
      have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]; exact htail

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/leastMap_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/sSupMaps_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem sSupMaps_le {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {h : ApproximableMap V₀ V₁} (hh : ∀ f ∈ F, f ≤ h) : sSupMaps F hF ≤ h := by
  intro X Y hrel
  obtain ⟨hX, hYmem⟩ := hrel
  have hle : supOnPrincipal F hF X hX ≤ h.toElementMap (V₀.principal hX) :=
    V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
      obtain ⟨f, hf, rfl⟩ := hs
      exact (le_iff_toElementMap_le.mp (hh f hf)) (V₀.principal hX)
  exact (h.rel_iff_mem_principal hX).mpr (hle Y hYmem)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/stepFun_subset_step_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Remark after Proposition 3.9 (Scott 1981, PRG-19).** When the neighbourhood is consistent,
`⋂ [Xᵢ, Yᵢ] ⊆ [X, Y]` iff `⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. This is the form used to check that `curry` is
monotone (and hence approximable). -/
theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toElementMap_curry_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.12(i) (Scott 1981, PRG-19).** `curry(g)(x)(y) = g(x, y)`. -/
theorem toElementMap_curry_apply (g : ApproximableMap (prod V₀ V₁) V₂)
    (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hyY, X, hxX, hX, _, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
    exact ⟨Y, hyY, X, hxX, x.sub hxX, step_mem (y.sub hyY) (g.rel_cod hrel), hrel⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toElementMap_sSupMaps_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toElementMap_sSupMaps_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    (sSupMaps F hF).toElementMap (V₀.principal hX) = supOnPrincipal F hF X hX :=
  toElementMap_ofMono_principal _ (supOnPrincipal_mono F hF) X hX

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toElementMap_sSupMaps.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toElementMap_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    (x : V₀.Element) :
    (sSupMaps F hF).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) := by
  apply le_antisymm
  · -- `(⊔F)(x) ⊑ ⊔{f(x)}`: read `(⊔F)(x)` off some principal `↑X` (Ex 2.9), where the
    -- principal value `(⊔F)(↑X) = ⊔{f(↑X)}` is bounded above by `⊔{f(x)}` (monotonicity, `↑X ⊑ x`).
    intro Y hY
    rw [toElementMap_mem_iff_principal (sSupMaps F hF) x] at hY
    obtain ⟨X, hxX, hY'⟩ := hY
    have hX : V₀.mem X := x.sub hxX
    rw [toElementMap_sSupMaps_principal hF] at hY'
    have hprinc : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    have hsub : supOnPrincipal F hF X hX ≤ V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) :=
      V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
        obtain ⟨f, hf, rfl⟩ := hs
        exact (toElementMap_mono f hprinc).trans (V₁.le_sSup _ (hF x) ⟨f, hf, rfl⟩)
    exact hsub Y hY'
  · -- `⊔{f(x)} ⊑ (⊔F)(x)`: `(⊔F)(x)` is an upper bound of every `f(x)` since `f ⊑ ⊔F` (3.13(i)).
    refine V₁.sSup_le _ (hF x) fun s hs => ?_
    obtain ⟨f, hf, rfl⟩ := hs
    exact le_iff_toElementMap_le.mp (le_sSupMaps hF hf) x

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toElementMap_sSupMapsu27.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** When `F` is bounded, `(⊔F)(x) = ⊔{f(x) ∣ f ∈ F}`
(stated with the boundedness hypothesis in Scott's `MapsBounded` form). -/
theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F) (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toElementMapu2082_eval.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter `φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    show φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/evalMap_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(⟨f, x⟩) = f(x)`. -/
theorem evalMap_apply (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalMap, ← toElementMap₂_toMap₂, toMap₂_ofMap₂, toElementMap₂_eval]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/toFilter_le_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toFilter_le_iff {f g : ApproximableMap V₀ V₁} : toFilter f ≤ toFilter g ↔ f ≤ g :=
  (funSpaceEquiv V₀ V₁).symm.map_rel_iff'

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/mapsBounded_to_filters.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/uncurry_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- `uncurry` is the composition `eval ∘ ⟨h ∘ p₀, p₁⟩`. -/
theorem uncurry_eq (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    uncurry h = (evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, evalMap_apply]
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W₀, hwW₀, hW₀, hrel⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW₀
    rw [inl_preimage_prodNbhd] at hrel
    rw [inr_preimage_prodNbhd] at hrel
    obtain ⟨hwX, hwY⟩ := (prod_mem_split hX hY).mp hwW₀
    exact ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
  · rintro ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
    refine ⟨prodNbhd X Y, (prod_mem_split hX hY).mpr ⟨hwX, hwY⟩, prod_mem_prodNbhd hX hY, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact hrel

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/curry_eval_comp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

end DomainTheory.NeighbourhoodSystems
end

section
-- FunctionSpace/eval_comp_curry.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.12(ii) (Scott 1981, PRG-19).** `eval ∘ ⟨curry(g) ∘ p₀, p₁⟩ = g`. -/
theorem eval_comp_curry (g : ApproximableMap (prod V₀ V₁) V₂) :
    (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g := by
  rw [← uncurry_eq]; exact uncurry_curry g

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise317/T.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/Token.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- Tokens of `T`: `{0, 1}`. -/
abbrev Token := Example12.Token

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/T_nbhd_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `T`-neighbourhoods are non-empty (`∅ ∉ T`). -/
theorem T_nbhd_nonempty {F : Set Token} (hF : T.mem F) : F.Nonempty := by
  rcases (Example12.mem_iff F).mp hF with rfl | rfl | rfl
  · exact ⟨0, by simp [Example12.master]⟩
  · exact ⟨0, by simp [Example12.zero]⟩
  · exact ⟨1, by simp [Example12.one]⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/bitNbhd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The `T`-neighbourhood selected by a bit: `false ↦ {0}`, `true ↦ {1}`. -/
def bitNbhd : Bool → Set Token
  | false => Example12.zero
  | true => Example12.one

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/bitNbhd_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem bitNbhd_mem (b : Bool) : T.mem (bitNbhd b) := by
  cases b
  · exact Example12.mem_zero
  · exact Example12.mem_one

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/encSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `encSet σ ⊆ ℕ × {0,1}`: pin copy `i` to `bitNbhd σ[i]` for `i < |σ|`, free otherwise. -/
def encSet (σ : Str) : Set (ℕ × Token) := {p | ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b}

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/mem_encSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem mem_encSet {σ : Str} {p : ℕ × Token} :
    p ∈ encSet σ ↔ ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/encSet_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem encSet_nil : encSet [] = Set.univ := by
  ext p; simp [encSet]

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/comparable_of_agree.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem comparable_of_agree : ∀ {τ τ' : Str},
    (∀ (i : ℕ) (b b' : Bool), τ[i]? = some b → τ'[i]? = some b' → b = b') → τ <+: τ' ∨ τ' <+: τ
  | [], _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _ => Or.inr (List.nil_prefix)
  | a :: s, a' :: s', hag => by
      have ha : a = a' := hag 0 a a' (by simp) (by simp)
      subst ha
      have hrec : ∀ (i : ℕ) (b b' : Bool), s[i]? = some b → s'[i]? = some b' → b = b' := by
        intro i b b' hb hb'
        exact hag (i + 1) b b' (by simpa using hb) (by simpa using hb')
      rcases comparable_of_agree hrec with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/encSet_agree.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- Two prefixes that both bound a common non-empty `T^∞`-neighbourhood agree where both defined. -/
theorem encSet_agree {τ τ' : Str} {W : Set (ℕ × Token)} (hW : (iterSys T).mem W)
    (h : W ⊆ encSet τ) (h' : W ⊆ encSet τ') {i : ℕ} {b b' : Bool}
    (hb : τ[i]? = some b) (hb' : τ'[i]? = some b') : b = b' := by
  obtain ⟨t, ht⟩ := T_nbhd_nonempty (hW.1 i)
  have h1 : t ∈ bitNbhd b := (h ht) b hb
  have h2 : t ∈ bitNbhd b' := (h' ht) b' hb'
  by_contra hne
  cases b <;> cases b' <;> simp_all [bitNbhd, Example12.zero, Example12.one]

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/encSet_anti.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- A longer prefix encodes to a *smaller* set: `σ ⪯ σ' ⟹ encSet σ' ⊆ encSet σ`. -/
theorem encSet_anti {σ σ' : Str} (h : σ <+: σ') : encSet σ' ⊆ encSet σ := by
  obtain ⟨t, rfl⟩ := h
  rintro ⟨i, x⟩ hp b hb
  have hi : i < σ.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb; exact hlt
  exact hp b (by rw [List.getElem?_append_left hi]; exact hb)

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/fiber_encSet_none.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem fiber_encSet_none {σ : Str} {i : ℕ} (h : σ[i]? = none) :
    fiber (encSet σ) i = Set.univ := by
  ext t
  simp only [mem_fiber, mem_encSet, Set.mem_univ, iff_true]
  intro b hb; rw [h] at hb; exact absurd hb (by simp)

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/fiber_encSet_some.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem fiber_encSet_some {σ : Str} {i : ℕ} {b : Bool} (h : σ[i]? = some b) :
    fiber (encSet σ) i = bitNbhd b := by
  ext t
  simp only [mem_fiber, mem_encSet]
  constructor
  · intro hh; exact hh b h
  · intro ht b' hb'; rw [h] at hb'; cases hb'; exact ht

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/encSet_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `encSet σ` is a `T^∞`-neighbourhood. -/
theorem encSet_mem (σ : Str) : (iterSys T).mem (encSet σ) := by
  refine ⟨fun i => ?_, σ.length, fun i hi => ?_⟩
  · cases h : σ[i]? with
    | none => rw [fiber_encSet_none h]; exact T.master_mem
    | some b => rw [fiber_encSet_some h]; exact bitNbhd_mem b
  · rw [fiber_encSet_none (List.getElem?_eq_none_iff.mpr hi)]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/f.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **The encoding map `f : B → T^∞`.** Relates the cone `σΣ*` to every `T^∞`-neighbourhood weaker
than `encSet σ`. -/
def f : ApproximableMap B (iterSys T) where
  rel X W := ∃ σ, X = cone σ ∧ (iterSys T).mem W ∧ encSet σ ⊆ W
  rel_dom := fun ⟨σ, hX, _⟩ => hX ▸ memB_cone σ
  rel_cod := fun ⟨_, _, hW, _⟩ => hW
  master_rel := ⟨[], cone_nil.symm, (iterSys T).master_mem, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro X W W' ⟨σ, hX, hWmem, hWsub⟩ ⟨σ', hX', hW'mem, hW'sub⟩
    obtain rfl : σ = σ' := cone_injective (hX.symm.trans hX')
    exact ⟨σ, hX, (iterSys T).inter_mem hWmem hW'mem (encSet_mem σ)
      (Set.subset_inter hWsub hW'sub), Set.subset_inter hWsub hW'sub⟩
  mono := by
    rintro X X' W W' ⟨σ, hX, _, hWsub⟩ hX'X hWW' hX' hW'mem
    obtain ⟨σ', rfl⟩ := hX'
    subst hX
    have hpre : σ <+: σ' := cone_subset_cone.mp hX'X
    exact ⟨σ', rfl, hW'mem, (encSet_anti hpre).trans (hWsub.trans hWW')⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/g.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **The decoding map `g : T^∞ → B`.** Relates `W` to the cone `τΣ*` exactly when `W ⊆ encSet τ`,
i.e. `W` pins the first `|τ|` copies to `τ`. -/
def g : ApproximableMap (iterSys T) B where
  rel W X := (iterSys T).mem W ∧ ∃ τ, X = cone τ ∧ W ⊆ encSet τ
  rel_dom h := h.1
  rel_cod := fun ⟨_, τ, hX, _⟩ => hX ▸ memB_cone τ
  master_rel := ⟨(iterSys T).master_mem, [], cone_nil.symm, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro W X X' ⟨hW, τ, hX, hWτ⟩ ⟨_, τ', hX', hWτ'⟩
    subst hX; subst hX'
    rcases comparable_of_agree (fun i b b' => encSet_agree hW hWτ hWτ') with hpre | hpre
    · exact ⟨hW, τ', by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr hpre)], hWτ'⟩
    · exact ⟨hW, τ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr hpre)], hWτ⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, τ, hX, hWτ⟩ hW₂W hXX₂ hW₂ hX₂
    obtain ⟨τ₂, rfl⟩ := hX₂
    subst hX
    have hpre : τ₂ <+: τ := cone_subset_cone.mp hXX₂
    exact ⟨hW₂, τ₂, rfl, hW₂W.trans (hWτ.trans (encSet_anti hpre))⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/exists_not_mem_bitNbhd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


theorem exists_not_mem_bitNbhd (b : Bool) : ∃ t : Token, t ∉ bitNbhd b := by
  cases b
  · exact ⟨1, by simp [bitNbhd, Example12.zero]⟩
  · exact ⟨0, by simp [bitNbhd, Example12.one]⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/fg_le_id.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 3.17 — `f` is a section of `g`.** `f ∘ g ⊑ I_{T^∞}`. -/
theorem fg_le_id : f.comp g ≤ idMap (iterSys T) := by
  intro W Z
  rw [comp_rel, idMap_rel]
  rintro ⟨X, ⟨hW, τ, hX, hWτ⟩, σ, hXσ, hZmem, hσZ⟩
  obtain rfl : τ = σ := cone_injective (hX.symm.trans hXσ)
  exact ⟨hW, hZmem, hWτ.trans hσZ⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/prefix_of_encSet_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Prefix recovery.** `encSet σ ⊆ encSet τ` forces `τ` to be an initial segment of `σ`. -/
theorem prefix_of_encSet_subset {σ τ : Str} (h : encSet σ ⊆ encSet τ) : τ <+: σ := by
  have hag : ∀ (i : ℕ) (b b' : Bool), σ[i]? = some b → τ[i]? = some b' → b = b' :=
    fun i b b' => encSet_agree (encSet_mem σ) subset_rfl h
  rcases comparable_of_agree hag with hστ | hτσ
  · by_cases hlen : σ.length = τ.length
    · exact (hστ.eq_of_length hlen) ▸ List.prefix_rfl
    · exfalso
      have hlt : σ.length < τ.length := lt_of_le_of_ne hστ.length_le hlen
      have hb' : τ[σ.length]? = some τ[σ.length] := List.getElem?_eq_getElem hlt
      obtain ⟨t, ht⟩ := exists_not_mem_bitNbhd τ[σ.length]
      have hmemσ : (σ.length, t) ∈ encSet σ := by
        intro b hb
        rw [List.getElem?_eq_none_iff.mpr (le_refl _)] at hb
        exact absurd hb (by simp)
      exact ht ((h hmemσ) _ hb')
  · exact hτσ

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/gf_eq_id.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 3.17 — `g` is a retraction of `f`.** `g ∘ f = I_B`. -/
theorem gf_eq_id : g.comp f = idMap B := by
  apply ApproximableMap.ext
  intro X Y
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨σ, hX, _, hσW⟩, _, τ, hY, hWτ⟩
    refine ⟨hX ▸ memB_cone σ, hY ▸ memB_cone τ, ?_⟩
    have hsub : encSet σ ⊆ encSet τ := hσW.trans hWτ
    rw [hX, hY]
    exact cone_subset_cone.mpr (prefix_of_encSet_subset hsub)
  · rintro ⟨hX, hY, hXY⟩
    obtain ⟨σ, rfl⟩ := hX
    obtain ⟨τ, rfl⟩ := hY
    have hpre : τ <+: σ := cone_subset_cone.mp hXY
    exact ⟨encSet σ, ⟨σ, rfl, encSet_mem σ, subset_rfl⟩,
      encSet_mem σ, τ, rfl, encSet_anti hpre⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

set_option linter.unusedVariables false

theorem example_317 : And
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B)) :=
  @And.intro
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B))
  DomainTheory.NeighbourhoodSystems.Exercise317.fg_le_id DomainTheory.NeighbourhoodSystems.Exercise317.gf_eq_id

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise317/f_injective.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **`f` is one-one.** Since `g ∘ f = I_B`, the elementwise map of `f` is injective. -/
theorem f_injective : Function.Injective f.toElementMap := by
  intro x y hxy
  have : (g.comp f).toElementMap x = (g.comp f).toElementMap y := by
    rw [toElementMap_comp, toElementMap_comp, hxy]
  rwa [gf_eq_id, toElementMap_idMap, toElementMap_idMap] at this

end DomainTheory.NeighbourhoodSystems.Exercise317
end

section
-- Exercise321/interYs_single_not_subset_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- For a single step `[Y, Z]` and an input `X ⊄ Y`, the intersection is the whole master `Δ₂`. -/
theorem interYs_single_not_subset_eq {YX : Set α} {Z : Set β} {X : Set α}
    (hXY : ¬ X ⊆ YX) : interYs V₁.master [(YX, Z)] X = V₁.master := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨hm, _⟩; exact hm
  · intro hz
    exact ⟨hz, fun p hp hXp => by rw [List.mem_singleton] at hp; subst hp; exact absurd hXp hXY⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/interYs_single_subset_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- For a single step `[Y, Z]` and a *sharp enough* input `X ⊆ Y`, the intersection is just `Z`. -/
theorem interYs_single_subset_eq {YX : Set α} {Z : Set β} {X : Set α} (hZ : V₁.mem Z)
    (hXY : X ⊆ YX) : interYs V₁.master [(YX, Z)] X = Z := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨_, hall⟩; exact hall (YX, Z) (List.mem_singleton.mpr rfl) hXY
  · intro hz
    exact ⟨V₁.sub_master hZ hz, fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; exact hz⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/stepCons.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Consistency (`hcons`) for a single step `[Y, Z]`: the intersection over the relevant outputs is
either `Z` (sharp input) or `Δ₂` (blunt input), both neighbourhoods. -/
theorem stepCons {Y : Set α} {Z : Set β} (hZ : V₁.mem Z) :
    ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master [(Y, Z)] X) := by
  intro X _
  by_cases hXY : X ⊆ Y
  · rw [interYs_single_subset_eq hZ hXY]; exact hZ
  · rw [interYs_single_not_subset_eq hXY]; exact V₁.master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/leastStep.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The single-step least map `f₀ ∈ [Y, Z]`: `leastMap [(Y, Z)]`, the minimal approximable mapping
relating `Y` to `Z`. -/
def leastStep (Y : Set α) (Z : Set β) (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    ApproximableMap V₀ V₁ :=
  leastMap [(Y, Z)] (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/leastStep_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem leastStep_le {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ step Y Z) : leastStep Y Z hY hZ ≤ f := by
  apply leastMap_le
  rw [stepFun_singleton]; exact hf

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/leastStep_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem leastStep_mem {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    leastStep Y Z hY hZ ∈ step Y Z := by
  have := leastMap_mem_stepFun (V₀ := V₀) (V₁ := V₁)
    (L := [(Y, Z)]) (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)
  rw [stepFun_singleton] at this
  exact this

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/leastStep_eq_of_step_eq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The least elements of equal step neighbourhoods coincide. -/
theorem leastStep_eq_of_step_eq {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z')
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') :
    leastStep Y Z hY hZ = leastStep Y' Z' hY' hZ' := by
  apply le_antisymm
  · exact leastStep_le hY hZ (h ▸ leastStep_mem hY' hZ')
  · exact leastStep_le hY' hZ' (h.symm ▸ leastStep_mem hY hZ)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/leastStep_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `f₀ = leastStep Y Z` relates `Y'` to `Z'` iff (`Y' ⊆ Y` and `Z ⊆ Z'`) or `Z' = Δ₂`. -/
theorem leastStep_rel {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (leastStep Y Z hY hZ).rel Y' Z' ↔ interYs V₁.master [(Y, Z)] Y' ⊆ Z' := by
  rw [leastStep, leastMap_rel]
  exact ⟨fun h => h.2.2, fun h => ⟨hY', hZ', h⟩⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/step_master_right.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.21.** If the output is the master, `[Y, Δ₂]` is the whole function space. -/
theorem step_master_right (Y : Set α) (hY : V₀.mem Y) :
    (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_step, Set.mem_univ, iff_true]
  exact f.mono f.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/step_eq_univ_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem step_eq_univ_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = Set.univ ↔ Z = V₁.master := by
  constructor
  · intro h
    -- the empty-list least map relates `Y` only to `Δ₂`; it lies in `[Y, Z] = univ`
    have hmem : leastMap (V₀ := V₀) (V₁ := V₁) ([] : List (Set α × Set β))
        (by simp) (fun {X} _ => by rw [interYs_nil]; exact V₁.master_mem) ∈ step Y Z := by
      rw [h]; exact Set.mem_univ _
    rw [mem_step, leastMap_rel] at hmem
    have : V₁.master ⊆ Z := by rw [← interYs_nil V₁.master Y]; exact hmem.2.2
    exact Set.Subset.antisymm (V₁.sub_master hZ) this
  · rintro rfl; exact step_master_right Y hY

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/step_eq_of_ne_master.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.21 (Scott 1981, PRG-19).** If `Z ≠ Δ₂`, the neighbourhood `[Y, Z]` determines both
endpoints: `[Y, Z] = [Y', Z']` implies `Y = Y'` and `Z = Z'`. -/
theorem step_eq_of_ne_master {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') (hZne : Z ≠ V₁.master)
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') : Y = Y' ∧ Z = Z' := by
  -- `Z' ≠ Δ₂` too, else `[Y', Z']` is the whole space and so is `[Y, Z]`, forcing `Z = Δ₂`
  have hZ'ne : Z' ≠ V₁.master := by
    intro hZ'eq
    rw [hZ'eq, step_master_right Y' hY'] at h
    exact hZne ((step_eq_univ_iff hY hZ).mp h)
  have hfeq := leastStep_eq_of_step_eq hY hZ hY' hZ' h
  -- `f₀.rel Y' Z'` and `f₀'.rel Y Z`, both with non-master outputs
  have h1 : (leastStep Y Z hY hZ).rel Y' Z' := by
    rw [hfeq]; exact (leastStep_mem hY' hZ')
  have h2 : (leastStep Y' Z' hY' hZ').rel Y Z := by
    rw [← hfeq]; exact (leastStep_mem hY hZ)
  rw [leastStep_rel hY hZ hY' hZ'] at h1
  rw [leastStep_rel hY' hZ' hY hZ] at h2
  -- from `h1`: `Y' ⊆ Y` and `Z ⊆ Z'`
  have hY'Y : Y' ⊆ Y := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h1
    exact hZ'ne (Set.Subset.antisymm (V₁.sub_master hZ') h1)
  have hZZ' : Z ⊆ Z' := by
    rw [interYs_single_subset_eq hZ hY'Y] at h1; exact h1
  -- from `h2`: `Y ⊆ Y'` and `Z' ⊆ Z`
  have hYY' : Y ⊆ Y' := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h2
    exact hZne (Set.Subset.antisymm (V₁.sub_master hZ) h2)
  have hZ'Z : Z' ⊆ Z := by
    rw [interYs_single_subset_eq hZ' hYY'] at h2; exact h2
  exact ⟨Set.Subset.antisymm hYY' hY'Y, Set.Subset.antisymm hZZ' hZ'Z⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321/step_eq_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.21 (Scott 1981, PRG-19).** The simple criterion for identity of function-space
neighbourhoods: `[Y, Z] = [Y', Z']` iff both outputs are the master `Δ₂`, or the pairs coincide. -/
theorem step_eq_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' ↔
      (Z = V₁.master ∧ Z' = V₁.master) ∨ (Y = Y' ∧ Z = Z') := by
  constructor
  · intro h
    by_cases hZeq : Z = V₁.master
    · refine Or.inl ⟨hZeq, ?_⟩
      rw [hZeq, step_master_right Y hY] at h
      exact (step_eq_univ_iff hY' hZ').mp h.symm
    · exact Or.inr (step_eq_of_ne_master hY hZ hY' hZ' hZeq h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [step_master_right Y hY, step_master_right Y' hY']
    · rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise321.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_321.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))
    @DomainTheory.NeighbourhoodSystems.step_eq_iff @DomainTheory.NeighbourhoodSystems.step_eq_of_ne_master)
  @DomainTheory.NeighbourhoodSystems.step_master_right

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322/compApp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The uncurried composition map `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, `⟨⟨g, f⟩, x⟩ ↦ g(f(x))`,
built from the inner evaluation `(𝒟₀→𝒟₁) × 𝒟₀ → 𝒟₁`, the outer evaluation `(𝒟₁→𝒟₂) × 𝒟₁ → 𝒟₂`,
and the product projections/pairing (Definition 3.3). -/
def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322/compMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The composition mapping
`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`, `comp = curry(compApp)`. -/
def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322/toElementMap_compApp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`. -/
theorem toElementMap_compApp (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (compApp V₀ V₁ V₂).toElementMap (pair (pair Gφ Fφ) x)
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compApp]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322/toElementMap_compMap_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 3.22 (Scott 1981, PRG-19).** `comp(g, f) = g ∘ f`: applying the value
`comp(⟨g, f⟩) ∈ |𝒟₀ → 𝒟₂|` to `x` gives `g(f(x))`. -/
theorem toElementMap_compMap_apply (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compMap, toElementMap_curry_apply, toElementMap_compApp]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322/toApproxMap_compMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 3.22 (Scott 1981, PRG-19).** The relational form `comp(g, f) = g ∘ f`: the value of
`comp` at `⟨g, f⟩`, read back as an approximable map, is the composition of the approximable maps. -/
theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise322.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_322.{u_1, u_2, u_3} : And
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x)))
  @DomainTheory.NeighbourhoodSystems.toApproxMap_compMap @DomainTheory.NeighbourhoodSystems.toElementMap_compMap_apply

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323/BasicInst4.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- There is at most one approximable mapping into the terminal domain `𝟙`: the codomain `|𝟙|`
is a subsingleton, so any two maps have the same elementwise action. -/
instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323/BasicInst5.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** `𝟙 = unitSys` is the *terminal object*: for every domain
`𝒟` there is a unique approximable mapping `𝒟 → 𝟙` (the constant map at `⊥`). -/
instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323/homAdjunction.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The cartesian-closed adjunction
`Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential object. This
is exactly `curryEquiv` of Theorem 3.12. -/
def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323/toUnit.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The unique map to the terminal object, named. -/
def toUnit : ApproximableMap V unitSys := default

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323/toUnit_unique.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise323.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_323.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys) f
    (@DomainTheory.NeighbourhoodSystems.toUnit α V) :=
  @DomainTheory.NeighbourhoodSystems.toUnit_unique

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324/funProdEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, `h ↦ (p₀ ∘ h, p₁ ∘ h)`. -/
def funProdEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap V₀ (prod V₁ V₂) ≃o (ApproximableMap V₀ V₁ × ApproximableMap V₀ V₂) where
  toFun h := ((proj₀ V₁ V₂).comp h, (proj₁ V₁ V₂).comp h)
  invFun p := paired p.1 p.2
  left_inv h := paired_proj h
  right_inv p := by
    ext1
    · exact proj₀_comp_paired p.1 p.2
    · exact proj₁_comp_paired p.1 p.2
  map_rel_iff' := by
    intro h h'
    constructor
    · rintro ⟨h0, h1⟩
      rw [← paired_proj h, ← paired_proj h']
      intro Z P hrel
      obtain ⟨hP, hfP, hgP⟩ := hrel
      exact ⟨hP, h0 _ _ hfP, h1 _ _ hgP⟩
    · intro hle
      refine ⟨fun X Y hrel => ?_, fun X Y hrel => ?_⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324/funProdIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)|`. -/
def funProdIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    (funSpace V₀ (prod V₁ V₂)).Element ≃o (prod (funSpace V₀ V₁) (funSpace V₀ V₂)).Element :=
  (funSpaceEquiv V₀ (prod V₁ V₂)).trans <|
    (funProdEquiv V₀ V₁ V₂).trans <|
      (prodCongrOrderIso (funSpaceEquiv V₀ V₁).symm (funSpaceEquiv V₀ V₂).symm).trans
        (prodEquiv (funSpace V₀ V₁) (funSpace V₀ V₂)).symm

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324/funProd_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 3.24(i).** `(𝒟₀ → (𝒟₁ × 𝒟₂)) ≅ (𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)`. -/
theorem funProd_isomorphic :
    funSpace V₀ (prod V₁ V₂) ≅ᴰ prod (funSpace V₀ V₁) (funSpace V₀ V₂) :=
  ⟨funProdIso V₀ V₁ V₂⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Sum β γ) V₀
      (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.funProd_isomorphic

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/exists_forall_swap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The `∃/∀`-swap behind `mapOfSeq`: a single input neighbourhood `X ∈ x` works for all coordinates
iff each coordinate has its own (intersect the finitely many non-trivial ones). -/
theorem exists_forall_swap {x : V₀.Element} {W : Set (ℕ × β)}
    {g : ℕ → ApproximableMap V₀ V₁} (hW : (iterSys V₁).mem W) :
    (∃ X, x.mem X ∧ ∀ i, (g i).rel X (fiber W i)) ↔
      (∀ i, ∃ X, x.mem X ∧ (g i).rel X (fiber W i)) := by
  constructor
  · rintro ⟨X, hXx, hall⟩ i; exact ⟨X, hXx, hall i⟩
  · intro hall
    obtain ⟨N, hN⟩ := hW.2
    choose Xs hXx hXrel using hall
    have hbase : x.mem (V₀.interUpTo Xs N) := x.mem_interUpTo Xs (n := N) (fun i _ => hXx i)
    refine ⟨V₀.interUpTo Xs N, hbase, fun i => ?_⟩
    by_cases h : i < N
    · exact (g i).mono (hXrel i) (V₀.interUpTo_subset Xs h) subset_rfl (x.sub hbase)
        ((g i).rel_cod (hXrel i))
    · rw [hN i (not_lt.mp h)]; exact (g i).rel_master (x.sub hbase)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/le_of_projComp_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A map `𝒟₀ → 𝒟₁^∞` is detected coordinate-wise: `f ⊑ f'` iff `projₙ ∘ f ⊑ projₙ ∘ f'` for all `n`. -/
theorem le_of_projComp_le {f f' : ApproximableMap V₀ (iterSys V₁)}
    (h : ∀ n, (projN V₁ n).comp f ≤ (projN V₁ n).comp f') : f ≤ f' := by
  rw [le_iff_toElementMap_le]
  intro x
  apply le_of_component_le
  intro n
  have hx := (le_iff_toElementMap_le.mp (h n)) x
  rwa [toElementMap_comp, toElementMap_comp, toElementMap_projN, toElementMap_projN] at hx

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/mapOfSeq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The "infinite pairing" map `𝒟₀ → 𝒟₁^∞` of a sequence `g : ℕ → Hom(𝒟₀, 𝒟₁)`:
`X (mapOfSeq g) W ↔ X ∈ 𝒟₀, W ∈ 𝒟₁^∞, and X gᵢ (fiber W i) for all i`. -/
def mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) : ApproximableMap V₀ (iterSys V₁) where
  rel X W := V₀.mem X ∧ (iterSys V₁).mem W ∧ ∀ i, (g i).rel X (fiber W i)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (iterSys V₁).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (g i).master_rel⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hrel⟩ ⟨_, hW', hrel'⟩
    refine ⟨hX, ⟨fun i => (g i).rel_cod ((g i).inter_right (hrel i) (hrel' i)), ?_⟩,
      fun i => (g i).inter_right (hrel i) (hrel' i)⟩
    obtain ⟨NW, hNW⟩ := hW.2
    obtain ⟨NW', hNW'⟩ := hW'.2
    refine ⟨max NW NW', fun i hi => ?_⟩
    rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
      hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  mono := by
    rintro X X' W W' ⟨_, _, hrel⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', fun i => (g i).mono (hrel i) hX'X (fiber_mono hWW' i) hX' (hW'.1 i)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/piCongrOrderIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A pointwise family of order-isomorphisms induces one on the dependent product. -/
def piCongrOrderIso {ι : Type*} {A B : ι → Type*} [∀ i, Preorder (A i)] [∀ i, Preorder (B i)]
    (e : ∀ i, A i ≃o B i) : (∀ i, A i) ≃o (∀ i, B i) where
  toFun f := fun i => e i (f i)
  invFun g := fun i => (e i).symm (g i)
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_rel_iff' := by
    intro f g
    exact ⟨fun h i => (e i).le_iff_le.mp (h i), fun h i => (e i).le_iff_le.mpr (h i)⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/projComp_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `projₙ ∘ f` is monotone in `f`. -/
theorem projComp_mono {f f' : ApproximableMap V₀ (iterSys V₁)} (h : f ≤ f') (n : ℕ) :
    (projN V₁ n).comp f ≤ (projN V₁ n).comp f' := by
  rintro X Y ⟨W, hfXW, hWY⟩
  exact ⟨W, h X W hfXW, hWY⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/toElementMap_mapOfSeq.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The value of `mapOfSeq g` is the sequence of values `⟨gᵢ(x)⟩`. -/
theorem toElementMap_mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) (x : V₀.Element) :
    (mapOfSeq g).toElementMap x = ofSeq (fun i => (g i).toElementMap x) := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hXx, _, hW, hrel⟩
    exact ⟨hW, fun i => ⟨X, hXx, hrel i⟩⟩
  · rintro ⟨hW, hfib⟩
    obtain ⟨X, hXx, hrel⟩ := (exists_forall_swap hW).mpr (fun i => hfib i)
    exact ⟨X, hXx, x.sub hXx, hW, hrel⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/funIterEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`, `f ↦ (n ↦ projₙ ∘ f)`. -/
def funIterEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (iterSys V₁) ≃o (∀ _ : ℕ, ApproximableMap V₀ V₁) where
  toFun f := fun n => (projN V₁ n).comp f
  invFun g := mapOfSeq g
  left_inv f := by
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_mapOfSeq]
    have hfun : (fun i => ((projN V₁ i).comp f).toElementMap x)
        = (fun i => component (f.toElementMap x) i) := by
      funext i; rw [toElementMap_comp, toElementMap_projN]
    rw [hfun, ofSeq_component]
  right_inv g := by
    funext n
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_comp, toElementMap_mapOfSeq, toElementMap_projN, component_ofSeq]
  map_rel_iff' := by
    intro f f'
    constructor
    · intro h; exact le_of_projComp_le (fun n => h n)
    · intro h n; exact projComp_mono h n

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/funIterIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → 𝒟₁^∞| ≃o |(𝒟₀ → 𝒟₁)^∞|`. -/
def funIterIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ (iterSys V₁)).Element ≃o (iterSys (funSpace V₀ V₁)).Element :=
  (funSpaceEquiv V₀ (iterSys V₁)).trans <|
    (funIterEquiv V₀ V₁).trans <|
      (piCongrOrderIso (fun _ : ℕ => (funSpaceEquiv V₀ V₁).symm)).trans
        (iterSeqEquiv (funSpace V₀ V₁)).symm

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter/funIter_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.24(ii).** `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`. -/
theorem funIter_isomorphic : funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  ⟨funIterIso V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise324Iter.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324_iter.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Prod Nat β) V₀
      (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Prod Nat β) V₀ (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @DomainTheory.NeighbourhoodSystems.funIter_isomorphic

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/leastMapVals.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.28 — the active values.** The set `{ ↑Yᵢ ∣ x ∈ [Xᵢ] }` of principal filters whose
input `Xᵢ` is a member of `x`. -/
def leastMapVals (L : List (Set α × Set β)) (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (x : V₀.Element) : Set V₁.Element :=
  {z | ∃ (p : Set α × Set β) (hp : p ∈ L), x.mem p.1 ∧ z = V₁.principal (hL p hp).2}

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/Elementu2emem_interYs_of.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A filter `z` contains the finite intersection `⋂{Yᵢ ∣ X ⊆ Xᵢ}` (inside `Δ₁`) as soon as it
contains each `Yᵢ` whose input `Xᵢ ⊇ X`. (The element-side analogue of `rel_interYs`.) -/
theorem Element.mem_interYs_of (z : V₁.Element) {L : List (Set α × Set β)} {X : Set α}
    (hall : ∀ p ∈ L, X ⊆ p.1 → z.mem p.2) : z.mem (interYs V₁.master L X) := by
  induction L with
  | nil => exact z.master_mem
  | cons p L ih =>
    have htail : ∀ q ∈ L, X ⊆ q.1 → z.mem q.2 :=
      fun q hq => hall q (List.mem_cons.mpr (Or.inr hq))
    by_cases hXp : X ⊆ p.1
    · have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]
      exact z.inter_mem (hall p (List.mem_cons.mpr (Or.inl rfl)) hXp) (ih htail)
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]
      exact ih htail

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/leastMap_toElementMap_le_of_ub.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `f₀(x)` is a *lower* bound of the upper bounds: any upper bound `z` of the active values
dominates `f₀(x)`. (Uses that `z` then contains `⋂{Yᵢ ∣ X ⊆ Xᵢ}`.) -/
theorem leastMap_toElementMap_le_of_ub {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element} {z : V₁.Element}
    (hz : ∀ w ∈ leastMapVals L hL x, w ≤ z) :
    (leastMap L hL hcons).toElementMap x ≤ z := by
  rintro Y' ⟨X', hX'x, hX'mem, hY'mem, hsub⟩
  have hzint : z.mem (interYs V₁.master L X') := by
    apply Element.mem_interYs_of
    intro p hp hX'p
    have hp1x : x.mem p.1 := x.up_mem hX'x (hL p hp).1 hX'p
    have hle : V₁.principal (hL p hp).2 ≤ z := hz _ ⟨p, hp, hp1x, rfl⟩
    exact hle p.2 ⟨(hL p hp).2, subset_rfl⟩
  exact z.up_mem hzint hY'mem hsub

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/val_le_leastMap_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- Each active value `↑Yᵢ` (with `Xᵢ ∈ x`) approximates `f₀(x)`, because `Yᵢ ∈ f₀(x)`. -/
theorem val_le_leastMap_toElementMap {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element}
    {p : Set α × Set β} (hp : p ∈ L) (hp1x : x.mem p.1) :
    V₁.principal (hL p hp).2 ≤ (leastMap L hL hcons).toElementMap x := by
  have hmem : ((leastMap L hL hcons).toElementMap x).mem p.2 :=
    ⟨p.1, hp1x, leastMap_mem_stepFun hL hcons p hp⟩
  intro Z hZ
  exact ((leastMap L hL hcons).toElementMap x).up_mem hmem hZ.1 hZ.2

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/leastMapVals_bounded.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The active values are bounded (by `f₀(x)`). -/
theorem leastMapVals_bounded {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    V₁.Bounded (leastMapVals L hL x) := by
  refine ⟨(leastMap L hL hcons).toElementMap x, ?_⟩
  rintro w ⟨p, hp, hp1x, rfl⟩
  exact val_le_leastMap_toElementMap hL hcons hp hp1x

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328/toElementMap_leastMap_eq_sSup.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.28 (Scott 1981, PRG-19).** The least map's elementwise action is the least upper
bound of the active principal filters: `f₀(x) = ⊔ { ↑Yᵢ ∣ x ∈ [Xᵢ] }`. -/
theorem toElementMap_leastMap_eq_sSup (L : List (Set α × Set β))
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    (leastMap L hL hcons).toElementMap x
      = V₁.sSup (leastMapVals L hL x) (leastMapVals_bounded hL hcons x) := by
  apply le_antisymm
  · apply leastMap_toElementMap_le_of_ub hL hcons
    intro w hw
    exact V₁.le_sSup _ (leastMapVals_bounded hL hcons x) hw
  · apply V₁.sSup_le
    rintro w ⟨p, hp, hp1x, rfl⟩
    exact val_le_leastMap_toElementMap hL hcons hp hp1x

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise328.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_328.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (L : List (Prod (Set α) (Set β)))
  (hL :
    ∀ (p : Prod (Set α) (Set β)),
      @Membership.mem (Prod (Set α) (Set β)) (List (Prod (Set α) (Set β))) (@List.instMembership (Prod (Set α) (Set β)))
          L p →
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Prod.fst (Set α) (Set β) p))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ (@Prod.snd (Set α) (Set β) p)))
  (hcons :
    ∀ {X : Set α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁
          (@DomainTheory.NeighbourhoodSystems.interYs α β
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) L X))
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
      (@DomainTheory.NeighbourhoodSystems.leastMap α β V₀ V₁ L hL fun {X : Set α} => @hcons X) x)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup β V₁
      (@DomainTheory.NeighbourhoodSystems.leastMapVals α β V₀ V₁ L hL x)
      (@DomainTheory.NeighbourhoodSystems.leastMapVals_bounded α β V₀ V₁ L hL (fun {X : Set α} => @hcons X) x)) :=
  @DomainTheory.NeighbourhoodSystems.toElementMap_leastMap_eq_sSup

end DomainTheory.NeighbourhoodSystems
end

section
-- graph.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **graph** of an approximable map, as a set of neighbourhood pairs. -/
def graph (f : ApproximableMap V₀ V₁) : Set (Set α × Set β) := {p | f.rel p.1 p.2}

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- mem_graph.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_graph {f : ApproximableMap V₀ V₁} {p : Set α × Set β} :
    p ∈ graph f ↔ f.rel p.1 p.2 := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- C.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's family `C`: all graphs of approximable maps `𝒟₀ → 𝒟₁`. -/
def C (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Set (Set (Set α × Set β)) :=
  Set.range (graph (V₀ := V₀) (V₁ := V₁))

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- C_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem C_nonempty : (C V₀ V₁).Nonempty :=
  ⟨graph (constMap V₀ V₁.bot), constMap V₀ V₁.bot, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- graph_injective.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem graph_injective : Function.Injective (graph (V₀ := V₀) (V₁ := V₁)) :=
  fun _ _ h => ApproximableMap.ext fun X Y => Set.ext_iff.mp h (X, Y)

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- graphEquiv.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `graph` is an order-isomorphism of approximable maps (under `⊑`) onto the family `C`
(under `⊆`). -/
noncomputable def graphEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ V₁ ≃o {X : Set (Set α × Set β) // X ∈ C V₀ V₁} where
  toFun f := ⟨graph f, f, rfl⟩
  invFun X := X.2.choose
  left_inv f := graph_injective (⟨graph f, f, rfl⟩ : {X // X ∈ C V₀ V₁}).2.choose_spec
  right_inv X := Subtype.ext X.2.choose_spec
  map_rel_iff' := by
    intro f g
    show graph f ⊆ graph g ↔ f ≤ g
    rw [ApproximableMap.le_iff]
    exact ⟨fun h X Y hf => h (a := (X, Y)) hf, fun h p hp => h p.1 p.2 hp⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- joinMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **join** `⋁ 𝒮` of a directed family of approximable maps: `X (⋁𝒮) Y` iff `(X, Y)` lies in
some member. Directedness is what restores the intersectivity condition (ii). -/
def joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒮) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_dom hp
  rel_cod := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_cod hp
  master_rel := by
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨S, hS, hp⟩ ⟨S', hS', hp'⟩
    obtain ⟨S₃, hS₃, hSS₃, hS'S₃⟩ := hdir S hS S' hS'
    obtain ⟨f, rfl⟩ := h𝒮 hS₃
    exact ⟨graph f, hS₃, f.inter_right (hSS₃ hp) (hS'S₃ hp')⟩
  mono := by
    rintro X X' Y Y' ⟨S, hS, hp⟩ hX'X hYY' hX' hY'
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.mono hp hX'X hYY' hX' hY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- meetMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The pointwise **meet** `⋀ 𝒮` of a family of approximable maps (drawn from `C`): `X (⋀𝒮) Y` iff
`(X, Y)` lies in every member of `𝒮`. -/
def meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty) :
    ApproximableMap V₀ V₁ where
  rel X Y := ∀ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_dom (h _ hS)
  rel_cod := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_cod (h _ hS)
  master_rel := by
    intro S hS; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.master_rel
  inter_right := by
    intro X Y Y' hY hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.inter_right (hY _ hS) (hY' _ hS)
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.mono (h _ hS) hX'X hYY' hX' hY'

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- sInter_eq_graph_meetMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sInter_eq_graph_meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) : ⋂₀ 𝒮 = graph (meetMap 𝒮 h𝒮 hne) := by
  ext p
  simp only [Set.mem_sInter, mem_graph]
  exact ⟨fun h S hS => h S hS, fun h S hS => h S hS⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- C_inter.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.22 hypothesis (i).** `C` is closed under non-empty intersections. -/
theorem C_inter : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ → ⋂₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮
  rw [sInter_eq_graph_meetMap 𝒮 h𝒮 hne]
  exact ⟨meetMap 𝒮 h𝒮 hne, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- sUnion_eq_graph_joinMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sUnion_eq_graph_joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) (hdir : DirectedOn (· ⊆ ·) 𝒮) :
    ⋃₀ 𝒮 = graph (joinMap 𝒮 h𝒮 hne hdir) := by
  ext p
  simp only [Set.mem_sUnion, mem_graph]
  exact ⟨fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩, fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- C_dir.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.22 hypothesis (ii).** `C` is closed under directed unions. -/
theorem C_dir : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ →
    DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮 hdir
  rw [sUnion_eq_graph_joinMap 𝒮 h𝒮 hne hdir]
  exact ⟨joinMap 𝒮 h𝒮 hne hdir, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- Exercise327.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


end DomainTheory.NeighbourhoodSystems.Exercise327

namespace DomainTheory.NeighbourhoodSystems.Exercise327

set_option linter.unusedVariables false

theorem example_327.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (𝒮 : Set (Set (Prod (Set α) (Set β)))),
  @Set.Nonempty (Set (Prod (Set α) (Set β))) 𝒮 →
    @LE.le (Set (Set (Prod (Set α) (Set β)))) (@Set.instLE (Set (Prod (Set α) (Set β)))) 𝒮
        (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) →
      @DirectedOn (Set (Prod (Set α) (Set β)))
          (fun (x1 x2 : Set (Prod (Set α) (Set β))) =>
            @LE.le (Set (Prod (Set α) (Set β))) (@Set.instLE (Prod (Set α) (Set β))) x1 x2)
          𝒮 →
        @Membership.mem (Set (Prod (Set α) (Set β))) (Set (Set (Prod (Set α) (Set β))))
          (@Set.instMembership (Set (Prod (Set α) (Set β))))
          (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) (@Set.sUnion (Prod (Set α) (Set β)) 𝒮) :=
  @DomainTheory.NeighbourhoodSystems.Exercise327.C_dir

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- funSpaceReprIso.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.27.** The function space `|𝒟₀ → 𝒟₁|` is (order-)isomorphic to the domain produced by
the *abstract* representation theorem (Exercise 2.22) applied to the family `C` of graphs of
approximable maps. This re-proves that approximable mappings form a domain without appealing to the
explicit step-set neighbourhood system of Definition 3.8 — composing Exercise 2.22's `reprIso` with
the graph isomorphism (`graphEquiv`) and Theorem 3.10 (`funSpaceEquiv`). -/
noncomputable def funSpaceReprIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (Exercise222.reprSystem (C V₀ V₁) C_inter C_nonempty).Element ≃o (funSpace V₀ V₁).Element :=
  (Exercise222.reprIso (C V₀ V₁) C_inter C_nonempty C_dir).trans
    ((graphEquiv V₀ V₁).symm.trans (funSpaceEquiv V₀ V₁).symm)

end DomainTheory.NeighbourhoodSystems.Exercise327
end

section
-- sierpinski.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

/-- The **Sierpiński domain** `𝒪`: the system over a one-token type whose neighbourhoods are `Δ`
(`univ`) and `∅`. Its elements are `⊥` (only `Δ`) and `⊤` (also `∅`), i.e. the two-point domain. -/
def sierpinski : NeighborhoodSystem Unit where
  mem N := N = Set.univ ∨ N = ∅
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ _
    rcases hX with rfl | rfl
    · rcases hY with rfl | rfl
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]
    · right; rw [Set.empty_inter]
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- mapOfOpen.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `mapOfOpen U : 𝒟 → 𝒪`. It always relates `X` to the blunt neighbourhood `univ` of `𝒪`, and
relates `X` to the sharp neighbourhood `∅` exactly when the basic open `[X]` lies inside `U`. As an
elementwise map it sends `x` to `⊤` iff `x ∈ U`. -/
def mapOfOpen (U : Set V.Element) : ApproximableMap V sierpinski where
  rel X Y := V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U))
  rel_dom h := h.1
  rel_cod h := by
    rcases h.2 with rfl | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  master_rel := ⟨V.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    refine ⟨hX, ?_⟩
    rcases hY with rfl | ⟨rfl, hsub⟩
    · rcases hY' with rfl | ⟨rfl, hsub'⟩
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]; exact ⟨rfl, hsub'⟩
    · rcases hY' with rfl | ⟨rfl, _⟩
      · right; rw [Set.inter_univ]; exact ⟨rfl, hsub⟩
      · right; rw [Set.inter_self]; exact ⟨rfl, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    rcases hY' with rfl | rfl
    · left; rfl
    · right
      refine ⟨rfl, ?_⟩
      rcases hY with rfl | ⟨rfl, hsub⟩
      · exact absurd (hYY' (Set.mem_univ ())) (by simp)
      · have hbo : V.basicOpen X' ⊆ V.basicOpen X := fun z hz => z.up_mem hz hX hX'X
        exact subset_trans hbo hsub

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- mapOfOpen_rel.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mapOfOpen_rel (U : Set V.Element) (X : Set α) (Y : Set Unit) :
    (mapOfOpen V U).rel X Y ↔ V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- mapOfOpen_rel_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The decisive special case: `X (mapOfOpen U) ∅ ↔ [X] ⊆ U` (for a neighbourhood `X`). -/
theorem mapOfOpen_rel_empty (U : Set V.Element) (X : Set α) :
    (mapOfOpen V U).rel X ∅ ↔ V.mem X ∧ V.basicOpen X ⊆ U := by
  rw [mapOfOpen_rel]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with h | ⟨_, h⟩
    · exact absurd h Set.empty_ne_univ
    · exact h
  · rintro ⟨hX, h⟩
    exact ⟨hX, Or.inr ⟨rfl, h⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- openOfMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `openOfMap f = {x ∣ f(x) = ⊤} = ⋃ {[X] ∣ X f ∅}`: the points sent by `f` to the top of `𝒪`. -/
def openOfMap (f : ApproximableMap V sierpinski) : Set V.Element :=
  {x | ∃ X, x.mem X ∧ f.rel X ∅}

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- openOfMap_isOpen.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `openOfMap f` is open: it is a union of basic opens `[X]`. -/
theorem openOfMap_isOpen (f : ApproximableMap V sierpinski) : IsOpen (openOfMap V f) := by
  constructor
  intro x hx
  obtain ⟨X, hxX, hf⟩ := hx
  exact ⟨X, hxX, fun z hz => ⟨X, hz, hf⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- Exercise325.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set


variable {α : Type*} (V : NeighborhoodSystem α)


end DomainTheory.NeighbourhoodSystems.Exercise325

namespace DomainTheory.NeighbourhoodSystems.Exercise325

set_option linter.unusedVariables false

theorem example_325.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V
      DomainTheory.NeighbourhoodSystems.Exercise325.sierpinski),
  @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
    (@DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap α V f) :=
  @DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap_isOpen

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- openIso.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.25 (core).** The open subsets of `|𝒟|` (ordered by `⊆`) are order-isomorphic to the
approximable maps `𝒟 → 𝒪`. -/
def openIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o ApproximableMap V sierpinski where
  toFun U := mapOfOpen V U.1
  invFun f := ⟨openOfMap V f, openOfMap_isOpen V f⟩
  left_inv U := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨X, hxX, hrel⟩
      rw [mapOfOpen_rel_empty] at hrel
      exact hrel.2 hxX
    · intro hx
      obtain ⟨X, hxX, hsub⟩ := U.2.out x hx
      exact ⟨X, hxX, (mapOfOpen_rel_empty V U.1 X).mpr ⟨x.sub hxX, hsub⟩⟩
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    rw [mapOfOpen_rel]
    constructor
    · rintro ⟨hX, hd⟩
      rcases hd with rfl | ⟨rfl, hsub⟩
      · exact f.mono f.master_rel (V.sub_master hX) (Set.subset_univ _) hX (Or.inl rfl)
      · have hpr : V.principal hX ∈ V.basicOpen X := ⟨hX, subset_rfl⟩
        obtain ⟨X', hX', hf⟩ := hsub hpr
        exact f.mono hf hX'.2 subset_rfl hX (Or.inr rfl)
    · intro hf
      refine ⟨f.rel_dom hf, ?_⟩
      rcases f.rel_cod hf with rfl | rfl
      · left; rfl
      · exact Or.inr ⟨rfl, fun z hz => ⟨X, hz, hf⟩⟩
  map_rel_iff' := by
    intro a b
    show mapOfOpen V a.1 ≤ mapOfOpen V b.1 ↔ a ≤ b
    rw [ApproximableMap.le_iff]
    constructor
    · intro h x hx
      obtain ⟨X, hxX, hsub⟩ := a.2.out x hx
      have hrelB := h X ∅ ((mapOfOpen_rel_empty V a.1 X).mpr ⟨x.sub hxX, hsub⟩)
      rw [mapOfOpen_rel_empty] at hrelB
      exact hrelB.2 hxX
    · intro h X Y hrel
      rw [mapOfOpen_rel] at hrel ⊢
      obtain ⟨hX, hd⟩ := hrel
      refine ⟨hX, ?_⟩
      rcases hd with hu | ⟨he, hsub⟩
      · exact Or.inl hu
      · exact Or.inr ⟨he, fun z hz => h (hsub hz)⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
end

section
-- opensReprIso.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.25.** The family of open subsets of `|𝒟|`, ordered by inclusion, is
order-isomorphic to the domain `|𝒟 → 𝒪|` of the Sierpiński function space — hence *is* (isomorphic
to) a domain. This uses Theorem 3.10 (`funSpaceEquiv`) exactly as Scott directs. -/
def opensReprIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o (funSpace V sierpinski).Element :=
  (openIso V).trans (funSpaceEquiv V sierpinski).symm

end DomainTheory.NeighbourhoodSystems.Exercise325
end
