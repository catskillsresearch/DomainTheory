module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_17b

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace ApproximableMap

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

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

end

end ApproximableMap

namespace NeighborhoodSystem

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

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

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

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

end ApproximableMap
end

section
set_option linter.unusedVariables false

theorem example_213.{u, u_1} : And
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x)) :=
  @And.intro
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x))
  (@And.intro
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.continuous_toElementMap
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem_iff_principal_of_continuous)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap_ofContinuous
end

end DomainTheory.NeighbourhoodSystems
