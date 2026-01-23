intro x h2
rw [mem_sUnion] at h2
obtain ⟨ t,ht ⟩ := h2
rw [mem_sUnion]
have h2 : t ∈ G := h1 ht.left
apply Exists.intro t
exact And.intro h2 ht.right
