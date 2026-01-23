intro x h
rw [mem_sUnion]
have hl:=h.left
rw [mem_sUnion] at hl
obtain ⟨s,hs⟩ := hl
have h2 := h1 s hs.left
obtain ⟨ u,hu ⟩ := h2
apply Exists.intro (s∩u)
constructor
exact hu.right
constructor
exact hs.right
have hr:= h.right
rw [mem_sInter] at hr
have h3 := hr u hu.left
exact h3
