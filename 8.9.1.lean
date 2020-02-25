open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open function

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) := (
  assume c: γ,
  let ⟨b, (hgb: g b = c)⟩ := hg c in
  let ⟨a, (hfa: f a = b)⟩ := hf b in
  have hc: (g ∘ f) a = c, by rsimp,
  ⟨a, hc⟩
).