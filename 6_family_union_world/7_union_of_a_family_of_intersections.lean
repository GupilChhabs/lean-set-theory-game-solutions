ext x
apply Iff.intro
intro h
rw [mem_sUnion]
have h1: x ∈  ⋃₀ F := h.right
rw [mem_sUnion] at h1
obtain ⟨ t,ht ⟩ := h1
apply Exists.intro (A∩t)
constructor
rw [mem_setOf]
apply Exists.intro t
constructor
exact ht.left
rfl
exact And.intro h.left ht.right
intro g
rw [mem_sUnion] at g
obtain ⟨ t,ht⟩ := g
have ht1 := ht.left
rw [mem_setOf] at ht1
obtain ⟨ u,hu⟩ := ht1
constructor
have hu2:=hu.right
rw [hu2] at ht
exact ht.right.left
rw [mem_sUnion]
apply Exists.intro u
constructor
exact hu.left
have hu2:=hu.right
rw [hu2] at ht
exact ht.right.right
