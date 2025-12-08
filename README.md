# Edge-Transitive Surfaces

This repository contains code and data used to construct the **census of edge-transitive surfaces**, as described in the accompanying research paper:

**Reymond Akpanya**  
*A Census of Edge-Transitive Surfaces*  
arXiv: https://arxiv.org/abs/2511.07631

This project provides computational tools (written in **GAP**) to generate, analyze, and verify the complete census.

---

## Repository Structure

### `RES2/`  
This directory contains the **census of edge-transitive surfaces**, where each surfaces is given as list of vertices of faces.

### `ConstructEdgeTransitiveSurfaces.gi`  
The main GAP source file providing the functions required to:  
- construct edge-transitive triangulated surfaces,  
- classify the surfaces up to isomorphism,  
- compute automorphism groups,  
- and generate the full census stored in `RES2/`.  

This is the core implementation of the algorithm described in the paper.

### `EulerO.g` and `EulerNO.g`  
These files contain the orientable (`EulerO.g`) and non-orientable (`EulerNO.g`) surfaces identified in the census.  
Each file includes data on Euler characteristics and genera of the computed surfaces.  

---

## Requirements

- **SimplicialSurfaces** (GAP package) — available at https://github.com/gap-packages/SimplicialSurfaces  

Make sure that the SimplicialSurfaces package (and its dependencies) are installed in your local GAP `pkg/` folder before using this repository.

---
