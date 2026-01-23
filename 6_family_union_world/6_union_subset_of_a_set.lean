constructor
intro h
intro s h1
intro x h2
apply h
rw [mem_sUnion]
apply Exists.intro s
exact And.intro h1 h2
intro h
intro x h1
rw [mem_sUnion] at h1
obtain ⟨ t ,ht ⟩ := h1
have h2: t ⊆ A := h t ht.left
exact h2 ht.right
