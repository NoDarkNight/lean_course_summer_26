# Handing in Exercise Solutions

Use one pull request per exercise sheet. Replace `n` by the sheet number and
replace `your-name` by your name.

0. Send me a DM on Discord or an email with a link to your GitHub profile, so
   that I can add you as a contributor to the repository.

1. Make sure you are on the `master` branch:

   ```bash
   git checkout master
   ```

2. Pull the latest version of the course repository:

   ```bash
   git pull
   ```

3. Create a new branch for your solutions:

   ```bash
   git checkout -b exercise-n-your-name
   ```

   For example:

   ```bash
   git checkout -b exercise-2-alex-smith
   ```

4. Solve the exercises.

5. Add and commit your changes:

   ```bash
   git add .
   git commit -m "your-name, exercise sheet n"
   ```

6. Push your branch:

   ```bash
   git push --set-upstream origin HEAD
   ```

7. Go to the GitHub repository in your web browser and create a pull request
   from your branch into `master`.

8. Select your TA as reviewer.

## If `master` was updated after you started working

If you already started solving the exercises and there were updates on the
`master` branch, update your exercise branch before continuing with the
exercises.

1. Commit your current work:

   ```bash
   git add .
   git commit -m "wip"
   ```

2. Go back to the `master` branch:

   ```bash
   git checkout master
   ```

3. Pull the latest version:

   ```bash
   git pull
   ```

4. Go back to your exercise branch:

   ```bash
   git checkout exercise-n-your-name
   ```

5. Rebase your exercise branch onto the updated `master` branch:

   ```bash
   git rebase master
   ```

6. If Git reports conflicts, resolve them using the graphical merge editor in
   VS Code. After resolving the conflicts, you can use the graphical interface
   of the VS Code merge editor to continue/complete the rebase.

   Alternatively, use the commands:

   ```bash
   git add .
   git rebase --continue
   ```

7. Once you are finished solving the exercises, continue with step 5 of handing in exercises.
