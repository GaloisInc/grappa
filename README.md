
# Building and Installing Grappa

Grappa currently only supports developer installs; see below.


# Building and Installing Grappa (Developers)

To do a developer install of Grappa:

1. Execute the supplied `build.sh` script from the Grappa distribution
   directory, with the following command:

```
./build.sh
```

2. Set the environment `GRAPPA_LIB` environment variable to point to the Grappa
   distribution directory. If you use the bash shell, you can do this by adding
   the following line to your `.bashrc` or `.bash_profile` (replacing the path
   with the actual path to the Grappa distribution) and then typing `source
   .bashrc` or `source .bash_profile` from the command line:

```
export GRAPPA_LIB=/path/to/Grappa
```


NOTE: Grappa (currently) depends on stack. Even if you build Grappa without
stack, the Grappa compiler itself calls stack to compile Grappa programs.


# Compiling a Grappa Program

To compile a Grappa program, use the following command:

```
stack exec grappa-c path/to/pgm.grappa
```

This will create an executable with the `.grappa` suffix removed. For instance,
the above command would create the file `path/to/pgm`.
