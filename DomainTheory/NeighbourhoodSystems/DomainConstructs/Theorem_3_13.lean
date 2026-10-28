module
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_27
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def MapsBounded (F : Set (ApproximableMap V₀ V₁)) : Prop := ∃ h, ∀ f ∈ F, f ≤ h

def PointwiseBounded (F : Set (ApproximableMap V₀ V₁)) : Prop :=
  ∀ x : V₀.Element, V₁.Bounded (Set.image (fun f => f.toElementMap x) F)

theorem mapsBounded_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    V₁.Bounded (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) :=
  hF (V₀.principal hX)

def supOnPrincipal (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X : Set α) (hX : V₀.mem X) : V₁.Element :=
  V₁.sSup (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) (mapsBounded_principal hF hX)

theorem supOnPrincipal_mono (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    supOnPrincipal F hF X hX ≤ supOnPrincipal F hF X' hX' :=
  V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
    obtain ⟨f, hf, rfl⟩ := hs
    exact (toElementMap_mono f ((V₀.principal_le_iff hX hX').mpr hX'X)).trans
      (V₁.le_sSup _ (mapsBounded_principal hF hX') ⟨f, hf, rfl⟩)

def sSupMaps (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) : ApproximableMap V₀ V₁ :=
  ofMono (fun X hX => supOnPrincipal F hF X hX) (supOnPrincipal_mono F hF)

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

theorem le_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ F) : f ≤ sSupMaps F hF := by
  intro X Y hrel
  have hX : V₀.mem X := f.rel_dom hrel
  have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
  exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hF hX) ⟨f, hf, rfl⟩) Y hmem⟩

theorem sSupMaps_le {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {h : ApproximableMap V₀ V₁} (hh : ∀ f ∈ F, f ≤ h) : sSupMaps F hF ≤ h := by
  intro X Y hrel
  obtain ⟨hX, hYmem⟩ := hrel
  have hle : supOnPrincipal F hF X hX ≤ h.toElementMap (V₀.principal hX) :=
    V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
      obtain ⟨f, hf, rfl⟩ := hs
      exact (le_iff_toElementMap_le.mp (hh f hf)) (V₀.principal hX)
  exact (h.rel_iff_mem_principal hX).mpr (hle Y hYmem)

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

theorem toElementMap_sSupMaps_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    (sSupMaps F hF).toElementMap (V₀.principal hX) = supOnPrincipal F hF X hX :=
  toElementMap_ofMono_principal _ (supOnPrincipal_mono F hF) X hX

theorem toElementMap_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    (x : V₀.Element) :
    (sSupMaps F hF).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) := by
  apply le_antisymm
  ·

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
  ·
    refine V₁.sSup_le _ (hF x) fun s hs => ?_
    obtain ⟨f, hf, rfl⟩ := hs
    exact le_iff_toElementMap_le.mp (le_sSupMaps hF hf) x

theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F) (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

theorem toFilter_le_iff {f g : ApproximableMap V₀ V₁} : toFilter f ≤ toFilter g ↔ f ≤ g :=
  (funSpaceEquiv V₀ V₁).symm.map_rel_iff'

theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

end
end DomainTheory.NeighbourhoodSystems
end
