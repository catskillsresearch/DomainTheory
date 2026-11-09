module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.liftSumRight
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

def sumLftCarrier (z : (sumSystem A B).Element) : Set α :=
  {x | SumToken.left x ∈ z.carrier}

def sumRhtCarrier (z : (sumSystem A B).Element) : Set β :=
  {y | SumToken.right y ∈ z.carrier}

theorem not_mem_right_of_mem_left (z : (sumSystem A B).Element)
    {x : α} {y : β} (hx : SumToken.left x ∈ z.carrier)
    (hy : SumToken.right y ∈ z.carrier) : False := by
  let u : Finset (SumToken α β) := insert (.left x) {SumToken.right y}
  have hsub : (↑u : Set _) ⊆ z.carrier := by
    intro p hp
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hp) with h | h
    · subst h; exact hx
    · have : p = .right y := Finset.mem_singleton.mp h
      subst this; exact hy
  have hCon := z.consistent u hsub
  have hlne : lftFinset u ≠ ∅ := by
    intro h
    have : x ∈ lftFinset u := (mem_lftFinset).2 (Finset.mem_insert_self _ _)
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hrne : rhtFinset u ≠ ∅ := by
    intro h
    have : y ∈ rhtFinset u :=
      (mem_rhtFinset).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [h] at this
    exact Finset.notMem_empty _ this
  rcases hCon with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hrne hr
  · exact hlne hl

theorem eq_botElement_of_no_injections (z : (sumSystem A B).Element)
    (hL : ∀ x : α, SumToken.left x ∉ z.carrier)
    (hR : ∀ y : β, SumToken.right y ∉ z.carrier) :
    z = (sumSystem A B).botElement := by
  apply le_antisymm
  · intro p hp
    cases p with
    | bot =>
      change SumToken.bot ∈ (sumSystem A B).botElement.carrier
      exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
    | left x => exact False.elim (hL x hp)
    | right y => exact False.elim (hR y hp)
  · exact botElement.le (sumSystem A B) z

theorem subset_botElement_of_projections_empty {u : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅) :
    (↑u : Set (SumToken α β)) ⊆ (sumSystem A B).botElement.carrier := by
  intro p hp
  have hp' : p ∈ u := Finset.mem_coe.1 hp
  cases p with
  | bot =>
    exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp'
      rw [hl] at this; exact Finset.notMem_empty _ this)
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp'
      rw [hr] at this; exact Finset.notMem_empty _ this)

def sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) : A.Element where
  carrier := sumLftCarrier A B z
  consistent := by
    intro Y hY
    have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (liftSumLeft.mem (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
      exact hY (Finset.mem_coe.2 hx)
    have h := SumCon.lft_mem_of_rht_empty A B (z.consistent _ hsub)
      (liftSumLeft.rhtFinset_eq (β := β) Y)
    rwa [liftSumLeft.lftFinset_eq] at h
  closed := by
    intro Y a hY hEnt
    if hempty : Y = ∅ then
      subst hempty
      have hEnt' : A.Ent {x0} a :=
        A.ent_trans (A.con_sing x0) A.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.left x0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .left x0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hx0
      have hSum : (sumSystem A B).Ent {SumToken.left x0} (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [lftFinset.singleton_left]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (liftSumLeft.mem (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
        exact hY (Finset.mem_coe.2 hx)
      have hSum : (sumSystem A B).Ent (liftSumLeft (β := β) Y) (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [liftSumLeft.lftFinset_eq]; exact hempty
        · rw [liftSumLeft.lftFinset_eq]; exact hEnt
      exact z.closed _ _ hsub hSum

def sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) : B.Element where
  carrier := sumRhtCarrier A B z
  consistent := by
    intro W hW
    have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (liftSumRight.mem (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
      exact hW (Finset.mem_coe.2 hy)
    have h := SumCon.rht_mem_of_lft_empty A B (z.consistent _ hsub)
      (liftSumRight.lftFinset_eq (α := α) W)
    rwa [liftSumRight.rhtFinset_eq] at h
  closed := by
    intro W b hW hEnt
    if hempty : W = ∅ then
      subst hempty
      have hEnt' : B.Ent {y0} b :=
        B.ent_trans (B.con_sing y0) B.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.right y0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .right y0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hy0
      have hSum : (sumSystem A B).Ent {SumToken.right y0} (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [rhtFinset.singleton_right]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (liftSumRight.mem (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
        exact hW (Finset.mem_coe.2 hy)
      have hSum : (sumSystem A B).Ent (liftSumRight (α := α) W) (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [liftSumRight.rhtFinset_eq]; exact hempty
        · rw [liftSumRight.rhtFinset_eq]; exact hEnt
      exact z.closed _ _ hsub hSum

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
