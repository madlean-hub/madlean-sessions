@echo off
REM Double-click this file to open the slides.
REM It starts a tiny local web server (required for the interactive info
REM panels and hovers to work) and opens the deck in your browser.
cd /d "%~dp0"

set PORT=8000
start "" "http://localhost:%PORT%/"

py -m http.server %PORT% 2>nul
if errorlevel 1 python -m http.server %PORT%
if errorlevel 1 (
  echo Python isn't installed. Install Python 3 from https://python.org,
  echo or open index.html directly ^(some features won't work without a server^).
  pause
)
