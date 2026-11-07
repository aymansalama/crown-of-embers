# Crown of Embers — War for the Ember Throne

An original medieval-fantasy grand-strategy game that runs in the browser. Five great houses fight over the realm of Aldmere, and each new game generates a fresh painted map.

**Play:** open `index.html` in any modern browser. It works on desktop and mobile, and needs no build step or network.

## Rules
- Pick a house. Each one has its own sigil, words and bonus.
- Tap one of your holdings, then tap a neighbouring land to march (if it's an enemy land, you attack). Dashed sea lanes connect the islands.
- **Levy Troops**: +5 troops for 10 gold. **Raise Walls**: +25% defence per level for 25 gold.
- Every 3 turns the season changes. In winter, income is halved and large armies lose troops to the cold.
- **Win** by holding Crownhold (the Ember Throne) for 3 consecutive turns, or by destroying every rival house.

Controls: drag to pan, scroll or pinch to zoom. Keys: `Enter` ends the turn, `R` levies, `F` fortifies, `Esc` deselects.

## Tech
Plain HTML, CSS and Canvas 2D. All art is generated procedurally at load time: the fBm heightmap terrain with hillshading, biomes, rivers, forests, mountains, old-map shoreline ripples, the warped-Voronoi regions, the house-colour border glow, and the particles. The fonts (Cinzel, Cormorant Garamond; SIL OFL) are bundled in `fonts/`.
