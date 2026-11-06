module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofMono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.iSupDirected
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

instance instNonemptyMemSubtype (x : V₀.Element) : Nonempty {X : Set α // x.mem X} :=
  ⟨⟨V₀.master, x.master_mem⟩⟩

/-- Continuous maps of ideal elements are monotone for approximation. -/
theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

theorem mem_iff_principal_of_continuous {c : V₀.Element → V₁.Element} (hc : Continuous c)
    (x : V₀.Element) {Y : Set β} :
    (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y := by
  constructor
  · intro hY
    have hxpre : x ∈ c ⁻¹' V₁.basicOpen Y := hY
    have hopen : IsOpen (c ⁻¹' V₁.basicOpen Y) := (V₁.isOpen_basicOpen Y).preimage hc
    obtain ⟨X, hxX, hXU⟩ := hopen.out x hxpre
    refine ⟨X, hxX, ?_⟩
    exact hXU (show V₀.principal (x.sub hxX) ∈ V₀.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
  · rintro ⟨X, hxX, hY⟩
    have hple : V₀.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact (continuous_monotone hc hple) Y hY

theorem principalFamily_directed (x : V₀.Element) :
    ∀ i j : {X : Set α // x.mem X}, ∃ k : {X : Set α // x.mem X},
      V₀.principal (x.sub i.2) ≤ V₀.principal (x.sub k.2) ∧
        V₀.principal (x.sub j.2) ≤ V₀.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V₀.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V₀.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

theorem eq_iSupDirected_principal (x : V₀.Element) :
    x = iSupDirected (fun i : {X : Set α // x.mem X} => V₀.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V₀.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V₀.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

/-- A monotone map that preserves indexed directed suprema is continuous. -/
theorem continuous_of_monotone_iSupDirected {c : V₀.Element → V₁.Element} (hmono : Monotone c)
    (hsup : ∀ {I : Type u} [Nonempty I] (d : I → V₀.Element)
      (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
      (hdir' : ∀ i j, ∃ k, c (d i) ≤ c (d k) ∧ c (d j) ≤ c (d k)),
      c (iSupDirected d hdir) = iSupDirected (fun i => c (d i)) hdir') :
    Continuous c := by
  rw [continuous_def]
  intro U hU
  constructor
  intro x hx
  rw [Set.mem_preimage] at hx
  set fam : {X : Set α // x.mem X} → V₀.Element := fun i => V₀.principal (x.sub i.2) with hfam
  have hdir : ∀ i j : {X : Set α // x.mem X}, ∃ k, fam i ≤ fam k ∧ fam j ≤ fam k :=
    principalFamily_directed x
  have hdir' : ∀ i j : {X : Set α // x.mem X}, ∃ k, c (fam i) ≤ c (fam k) ∧ c (fam j) ≤ c (fam k) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hdir i j; exact ⟨k, hmono hik, hmono hjk⟩
  have hxeq : c x = iSupDirected (fun i => c (fam i)) hdir' :=
    (congrArg c (eq_iSupDirected_principal x)).trans
      (hsup (I := {X : Set α // x.mem X}) fam hdir hdir')
  rw [hxeq] at hx
  obtain ⟨Y, hY, hYU⟩ := hU.out _ hx
  obtain ⟨i, hi⟩ := (mem_iSupDirected _ hdir').mp hY
  refine ⟨i.1, i.2, fun x' hx' => hYU ?_⟩
  have hple : fam i ≤ x' := fun Z hZ => x'.up_mem hx' hZ.1 hZ.2
  exact (hmono hple) Y hi

end

end NeighborhoodSystem

namespace ApproximableMap

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Approximable map induced by a continuous map of ideal elements. -/
def ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c) : ApproximableMap V₀ V₁ :=
  ofMono (fun _X hX => c (V₀.principal hX))
    (fun _X _X' hX hX' hX'X =>
      NeighborhoodSystem.continuous_monotone hc ((V₀.principal_le_iff hX hX').mpr hX'X))

theorem continuous_toElementMap (f : ApproximableMap V₀ V₁) :
    Continuous (fun x => f.toElementMap x) := by
  rw [continuous_def]
  intro U hU
  show V₀.OpenFilter _
  constructor
  intro x hx
  obtain ⟨Y, hY, hYU⟩ := hU.out (f.toElementMap x) hx
  obtain ⟨X, hxX, hrel⟩ := hY
  exact ⟨X, hxX, fun x' hx' => hYU ⟨X, hx', hrel⟩⟩

theorem toElementMap_ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c)
    (x : V₀.Element) : (ofContinuous c hc).toElementMap x = c x := by
  apply Element.ext
  intro Y
  rw [toElementMap_mem_iff_principal, NeighborhoodSystem.mem_iff_principal_of_continuous hc]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal] at hmem
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal]

end

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
