This folder contains scripts and instructions for setting up a docker container for agent-based development of this project.
We assume that you are working from a laptop and have a desktop or server machine with a few hundred GB of free disk space, and that you can log into that machine (called "host" in this document) via ssh keys registered via `ssh-agent` and copied to the host using `ssh-copy-id`.

This folder contains the few files that you will need on the host *outside* of the container. Start by copying them from your laptop to the host:

```
rsync -avz --delete /your/path/to/ADTF/setup/adtf2-sandbox/ username@yourserver:/path/to/setupstuff/adtf2-sandbox/
```

Note that this command will delete files at the host path that are not in the source path (first argument).

Then ssh into the host and cd into the `docker` subfolder of this setup folder you just copied. Run `ls` to confirm that it contains only one file, `Dockerfile`.

In that directory, run

```
docker build -t "$(whoami)-adtf2-image" .
```

Note that we prefix all names used by docker with `$(whoami)`, because on servers, the docker names of images, volumes and containers are one same namespace shared among all users.

After that, `docker images` should display all images you have, including the one you just built.

Next, we need to create a volume for the container. If we don't create a volume explicitly, docker will create one in its default location (which might be a small system partition instead of your potentially bigger home partition).
In this example, we create the volume in our home folder:

```
mkdir -p ~/docker-volumes/adtf2-volume
docker volume create --driver local \
  --opt type=none --opt o=bind --opt device=~/docker-volumes/adtf2-volume \
  "$(whoami)-adtf2-volume"
```

To list your volumes, including the one just created:

```
docker volume inspect --format '{{.Name}}: {{or .Options.device .Mountpoint}}' $(docker volume ls -q)
```

This prints `.Options.device` whenever a custom path is configured, and falls back to `.Mountpoint` for standard Docker-managed volumes.

Now, let's create and start the container:

```
docker run -dit --init --name "$(whoami)-adtf2-sandbox" \
  --cap-drop ALL --security-opt no-new-privileges \
  --pids-limit 4096 --memory 24g \
  -p 127.0.0.1::8100 \
  --mount type=volume,source="$(whoami)-adtf2-volume",target=/home/ubuntu \
  "$(whoami)-adtf2-image"
```

Make sure you set the memory limit well below the available RAM on your host machine. If you ask an agent to write Lean proofs about assembly code, it is likely to call `simp` on expressions that unfold to such huge terms that Lean consumes seemingly unbounded amounts of RAM, which can lock up your container, and if the memory limit of the container is too big, it can also lock up your host so that you cannot even ssh into it anymore.

Claude's explanation of what each option does:

- `-d` (detach) runs the container in the background and returns you to your shell.
- `-i` keeps the main process's input open, and `-t` gives it a terminal. Together they keep the idle `bash` from exiting, so the container stays up.
- `--init` runs a tiny init process as PID 1, which passes on signals and cleans up finished processes.
- `--name` gives the container its name.
- `--cap-drop ALL` removes all Linux capabilities, and `--security-opt no-new-privileges` prevents gaining privileges through setuid programs.
- `--pids-limit` and `--memory` cap the number of processes and the memory, so a runaway agent can't take down the server.
- `-p 127.0.0.1::8100` publishes port 8100 on the server's loopback only. 8100 must match the `--port` of `code serve-web` described later. The server port is left empty, so Docker picks a free one and users can't clash. It changes every time the container starts.
- `--mount` attaches the volume as the home directory. If the volume does not exist yet, it is automatically created.
- The last argument is the image.

To list all containers (`-a` to include stopped ones):

```bash
docker ps -a
```

The above commands are all one-time setup commands. On the other hand, these are the commands you'll need more regularly:

* `./new-shell.sh`: Creates a new shell inside the container (best used in a new tmux tab, tmux running on the host)
* `./serve-web.sh`: Starts a server for a browser-based VS code UI, allowing you to inspect the code the agent is working on
* `docker stop "$(whoami)-adtf2-sandbox"`: stops the container (needed eg if it ran out of memory), the volume persists
* `docker start "$(whoami)-adtf2-sandbox"`: restarting the container (needed eg after `stop`, after a docker update that restarted docker, or after a host reboot)

In a new shell inside the container, install Claude (or whatever your favorite LLM agent is):

```
curl -fsSLo /tmp/install-claude.sh https://claude.ai/install.sh
cat /tmp/install-claude.sh
bash /tmp/install-claude.sh
```
