#!/bin/sh
cd src
graphmod Kant/REPL.hs | dot -T pdf -o modules.pdf
mv modules.pdf ..