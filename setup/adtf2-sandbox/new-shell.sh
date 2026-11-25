#!/bin/bash

# The first "exec" is a bash command to replace the current bash by the docker process,
# so that tmux displays "docker" instead of "bash" and you can distinguish what tmux
# tabs are host vs container.
exec docker exec -it "$(whoami)-adtf2-sandbox" bash
