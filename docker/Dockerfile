from ubuntu:14.04

copy SHA256SUMS /usr/local/ghc/
copy get-ghc /usr/local/bin/
copy config known_hosts docker_id /root/.ssh/
# TODO: Why the heck is this needed? The docs for add say the new files will
# have uid/gid 0/0, but /root/.ssh/config seems to have 1000/1000!
run chown root:root /usr/local/ghc/SHA256SUMS /usr/local/bin/get-ghc /root/.ssh/*

run apt-get update
run apt-get install -y wget python-pip git libgmp-dev zlib1g-dev pkg-config python-dev libncurses5-dev r-base

workdir /tmp
run get-ghc
run wget http://hackage.haskell.org/package/cabal-install-1.24.0.0/cabal-install-1.24.0.0.tar.gz
run wget https://github.com/zeromq/zeromq4-1/releases/download/v4.1.5/zeromq-4.1.5.tar.gz
run git clone gitlab-int:ppaml/monad-ppl
run tar xf ghc-7.10.3b-x86_64-deb8-linux.tar.xz
run tar xf cabal-install-1.24.0.0.tar.gz
run tar xf zeromq-4.1.5.tar.gz

workdir /tmp/ghc-7.10.3
run ./configure
run make install

workdir /tmp/cabal-install-1.24.0.0
run ./bootstrap.sh --no-doc
env PATH /root/.cabal/bin:$PATH

workdir /tmp/zeromq-4.1.5
run ./configure
run make -j
run make install
run ldconfig

run pip install ipython[all]

workdir /tmp/monad-ppl
run cabal update
run cabal install -j8 stack
env STACK "stack --stack-yaml stack-ghc-7.10.yaml"
run $STACK build c2hs hsc2hs
run $STACK build ihaskell-inline-r
run $STACK exec ihaskell install
run $STACK build --only-dependencies
expose 8888

# Why pull again? This improves docker's behavior when bumping the commit
# number below. Without the re-pull, docker will use the cached result of git
# clone above, and the git checkout will probably fail. But since these two
# lines are together, there's no cache "in between" the git pull and git
# checkout commands, so when the commit number changes the git pull will be
# redone.
#
# This problem could also be dealt with by putting the checkout and the clone
# together into one command, rather than having one clone command and having
# one pull-and-checkout combined command. However, with docker you generally
# want to invalidate caches as late as possible; in particular, we'd like to
# cache the building of the ihaskell stuff and other dependencies, since in the
# common case those don't change just because we bumped the monad-ppl version.
run git pull && git checkout a32a3628
run $STACK build

cmd $STACK exec jupyter -- notebook --ip 0.0.0.0 --notebook-dir /mnt
