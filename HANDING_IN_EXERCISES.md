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
