rpylean: Building Your Own Lean Kernel for Fun
==============================================

An interactive slide deck (reveal.js). To open it:

  macOS    Double-click  "Start Slides (macOS).command"
  Windows  Double-click  "Start Slides (Windows).bat"
  Linux    Run           bash start-slides-linux.sh

Your browser opens at http://localhost:8000/. Keep the little terminal/
console window open while presenting; close it when you're done.

Why a server instead of just opening index.html?
-------------------------------------------------
The interactive Lean features need it. Without a server, browsers block
the deck from loading its data and the panels/hovers come up empty.

If a launcher doesn't work (no Python installed), you can still open
index.html directly in a browser to read the slides -- but the
interactive bits below won't function.

Using the deck
--------------
  Arrow keys / Space   move between slides
  F                    fullscreen
  S                    speaker notes view
  ESC or O             slide overview

Seeing the Lean "infoview":
  - Click a token in a code block to pin its type / goal state in the
    panel beside the code. Clicking again steps out to the enclosing term.
  - Hover an identifier for its type, a tactic for the proof goal state,
    or a #check result for its output.
