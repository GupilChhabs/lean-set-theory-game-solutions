obtain ⟨ s ,hs ⟩ := h2
apply Exists.intro s
constructor
exact hs.left
have h2 := h1 s hs.left
obtain ⟨ t,ht ⟩ := h2
have hsr:= hs.right
have h3 := hsr t ht.left
have h4 := Subset.antisymm ht.right h3
rw [h4]
exact ht.left
