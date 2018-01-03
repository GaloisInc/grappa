This is a docker container that exposes an iHaskell notebook server with access to the monad-ppl codebase. To do that, it needs to be able to pull from the monad-ppl repository. Eventually, that repository will be marked public (which will mean "public to actors on the Galois VPN", not "public to the world"), and nothing special will be needed to pull from it. But for now it is private. So you will need to do some setup before doing the usual docker things (see below for a "docker quickstart" in case you don't know what the usual docker things are).

The docker container needs an SSH key that can pull from the monad-ppl repository. You can copy in your personal key or create a fresh one and list it as a deploy key on gitlab-int. For the former, run

    cp ~/.ssh/id_rsa docker_id

(or similar if your private key is named something other than `id_rsa`). For the latter, run

    ssh-keygen -t rsa -b 4096 -f docker_id

then visit https://gitlab-int.galois.com/ppaml/monad-ppl/deploy_keys and paste the contents of `docker_id.pub` there.

Now you're ready to do the usual docker things. First build everything with:

    docker build -t ihaskell-ppl .

You'll want to go play some pinball while you wait for this one; it takes a while. Once it's done, you can start up the iHaskell notebook server:

    docker run -p 8888:8888 -v notebooks:/mnt -t ihaskell-ppl

Then open up a browser and visit http://localhost:8888/. A brief overview of the options used here:

* `run` says to create a new docker container from an image and run a command in it (in this case, the command specified at the end of `Dockerfile`).
* `-p 8888:8888` forwards port 8888 from inside the docker container to the host system's port 8888; this lets you access the Jupyter server from the host system.
* ` -v notebooks:/mnt` creates a data volume named `notebooks` and mounts it inside the docker container's filesystem under the path `/mnt`; if you later stop the container and start a new one (perhaps after building an updated version of monad-ppl) this will allow notebooks to persist. The command specified at the end of `Dockerfile` tells Jupyter to look in `/mnt` for notebooks.
* `-t` allocates a TTY; this is just cosmetic.
* `ihaskell-ppl` selects the image we created earlier with `docker build` to serve as the basis of the new container.

Can't find the docker daemon during `docker build`? Start it up via your init system; `systemctl start docker` as root on `systemd` boxes. Permission problems during `docker build`? Add yourself to the `docker` group (`sudo usermod -aG docker $(whoami)`, then log out and back in) or use `sudo`.

Want to use a different version of monad-ppl? There is a line towards the end of the `Dockerfile` that specifies which commit will be built; look for and change it:

    run git pull && git checkout <COMMIT>
