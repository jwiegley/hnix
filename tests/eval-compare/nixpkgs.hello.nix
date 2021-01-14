/*

FIXME: TODO: This is a bad test because:

1. We may not have access to the network in test environments (e.g. Nix :-))
2. fetchTarball is not yet implemented in hnix and call the real nix
3. We want all the tests that rely on nixpkgs to use the same fetched path
4. We want a single place to update the nixpkgs revision we test.
5. Currently hnix tests are not sandboxed as the ones in hnix-store-remote,
   so all the .drv we build en up in the host store.

 XXX: NIXPKGS_TESTS are broken for now. Fix that too when fixing this.

*/
let 
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/1dc37370c489b610f8b91d7fdd40633163ffbafd.tar.gz";
  };
in
  
with import nixpkgs {};
"${pkgs.hello.drvPath}"
