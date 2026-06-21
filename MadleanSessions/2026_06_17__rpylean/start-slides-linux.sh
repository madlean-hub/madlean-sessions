#!/bin/bash
# Run this to open the slides:  bash start-slides-linux.sh
# It starts a tiny local web server (required for the interactive info
# panels and hovers to work) and opens the deck in your browser.
cd "$(dirname "$0")" || exit 1

PORT=8000
PY=""
if command -v python3 >/dev/null 2>&1; then PY="python3"
elif command -v python >/dev/null 2>&1; then PY="python"
else
  echo "Python isn't installed. Install Python 3, or open index.html directly"
  echo "(some interactive features won't work without a server)."
  exit 1
fi

echo "Serving slides at http://localhost:$PORT/"
echo "Leave this terminal open while presenting. Press Ctrl-C to stop."
"$PY" -m http.server "$PORT" >/dev/null 2>&1 &
SERVER_PID=$!
sleep 1
xdg-open "http://localhost:$PORT/" >/dev/null 2>&1 || \
  echo "Open http://localhost:$PORT/ in your browser."
trap 'kill $SERVER_PID 2>/dev/null' EXIT
wait $SERVER_PID
