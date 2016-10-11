# 2IMI25: Constraint Programming - Assignment 2

This is the source repository for the second assignment for the TUE course 2IMI25: Constraint Programming. The repository should contain the data files and the model file for the OPL project.


## Git commands
Some helpful git commands to get started with this repository are also listed here.

### Initializing the project
1. Make sure hat git is installed: https://git-scm.com/downloads
2. Open a command line (in windows, you can use Git Bash which is included with git).
3. navigate to the folder where you want to put the project.
4. Set your default username and email address by executing the following commands:
  1. `git config --global user.email "[email address]"` Replace `[email address]` by your email address used with github.
  2. `git config --global user.name "[github username]"` Replace `[github username]` by your github username.
5. execute `git clone https://github.com/vanLankveld/2imi25_assignment_2` use your github username and password if asked. This will create a new folder with the source files from github
6. Create a new OPL project with CPLEX Optimization Studio in this folder using the exising model and data files.

### Pulling
To update your model file and to include all modifications made by other group members:

1. open a command line.
2. navigate to the project folder (which is the folder that was created with the `clone` command).
3. execute `git pull`.

### Committing and pushing
To update the file on github, so other group members can see your changes: 

1. open a command line.
2. navigate to the project folder and 
3. execute `git add [filename]`, replacing `[filename]` with the file that you gave edited (do this for every edited file). You can also execute `git add *` if you want to add all files that you have changed or created.
5. execute `git commit -m "[message]"` replacing `[message]` with a short description of what you have changed or added
6. execute `git pull` to also include changes made by others. 
7. execute `git push`

###**Always do `git pull` when you start working and right after a `git commit` before you do `git push`!**
