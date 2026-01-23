ext x
apply Iff.intro
intro h
rw [mem_sInter]
intro t
intro h1
rw [mem_pair] at h1
rcases h1 with h1a|h1b
rw [h1a]
exact h.left
rw [h1b]
exact h.right
intro h
rw[mem_sInter] at h
constructor
have hAinAB : A ∈ {A,B}
rw [mem_pair]
left
rfl
exact h A hAinAB
have hBinAB : B ∈ {A,B}
rw [mem_pair]
right
rfl
exact h B hBinAB
