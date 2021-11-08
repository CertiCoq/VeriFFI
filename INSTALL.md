# Installation instructions

Currently the recommended way to build the VeriFFI project is through Docker containers.

Here are the necessary steps:

1. [Install Docker on your machine.](https://docs.docker.com/get-docker/)
2. Start the Docker.
3. Download our image by running `docker pull cattheory/veriffi` in your terminal.
   This image currently has Opam 2.0.0, OCaml 4.07.1, Coq 8.13.2, CompCert 3.9, VST 2.8 (from `master`), MetaCoq's branch for Coq 8.13, Coq-Ext-Lib 0.11.4.
   It doesn't yet have CertiCoq because it is not compatible with the software listed here. It will once CertiCoq is updated to work with them. (MetaCoq is the main showstopper here.)
4. Create a workspace folder in which you will have the files you want to run in the container. 

   For these instructions, we will assume they are in `~/container`. Feel free to clone this repo into that folder by
   ```
   cd ~/container
   git clone https://github.com/CertiCoq/VeriFFI.git
   ```
5. You can navigate to that folder in your terminal (if you haven't done it in the previous step) and then create a Docker container with these commands:
   
   ```
   cd ~/container
   docker run -ti -v $(pwd):/tmp --name vf cattheory/veriffi
   ```
   This will take you to a bash session inside the container.
6. When you are inside that bash session, you can find the files in your host machine's `~/container` directory in `/tmp` in the container.
   Any change you make on the host will appear in the container and vice versa. For example, you can compile the VeriFFI project inside the container by running
   ```
   cd /tmp/VeriFFI
   coqc $(cat _CoqProject) 
   ```
7. Exiting the bash session will terminate the container but you can restart it anytime in the background by running
   ```
   docker restart vf
   ```
   If you want to access the container bash session again, you can run
   ```
   docker exec -ti vf /bin/bash
   ```
8. If you want to use Emacs in your host machine to edit files in the container and run the Coq version in the container,
   you need to use the [docker.el](https://github.com/Silex/docker.el) package for Emacs.
   
   If you're using Spacemacs, you can just add it to the additional packages list:
   ```lisp
   (setq-default dotspacemacs-additional-packages '(company-coq
                                                    docker
                                                   ))
   ```
   If you're not using such an Emacs distribution, you can use [use-package](https://github.com/jwiegley/use-package) or more traditional methods to install that package.
   
   Once you do, you will also want to add this to your `.emacs` (or `.spacemacs`) file:
   
   ```lisp
   (defun set-coqtop-docker ()
    (if (string-prefix-p "/docker:vf:" (buffer-file-name))
      (setq coq-prog-name "/home/opam/.opam/4.07.1/bin/coqtop")
      (setq coq-prog-name "coqtop")
     ))

   (add-hook 'coq-mode-hook 'set-coqtop-docker)
   ```
   This function checks every time you start Coq mode for a file, whether that file is from our Docker container,
   and if it is, it sets a hard path for the `coqtop` program that allows Emacs to communicate with Coq. If not, it just uses the `coqtop` on your host machine.
   This way you can use the Coq version on your host machine and the Coq version in your container with the same settings.
   
   Do not be confused by the hard path in the code above, it is a path inside the Docker container.
   
 9. That's it!
    
    You can now load a file (C-x C-f) in Emacs from the Docker container by typing `/docker:vf:/tmp/` (complete it yourself) and you should be able to open any file from `~/container/` but using the Coq version in the container.
   
   
   
