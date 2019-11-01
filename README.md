![Logo](https://avatars3.githubusercontent.com/u/30268214?v=4&s=200)
[![Build Status](https://travis-ci.org/AlloyTools/org.alloytools.alloy.svg?branch=master)](https://travis-ci.org/AlloyTools/org.alloytools.alloy)
# Alloy

Alloy 4 is a self-contained executable, which includes the Kodkod
model finder and a variety of SAT solvers, as well as the standard
Alloy library and a collection of tutorial examples. The same jar file
can be incorporated into other applications to use Alloy as an API,
and includes the source code. See the release notes for details of new
features. 

More documentation can be found at: http://alloytools.org/documentation.html.

# Requirements

Alloy runs on all operating systems with a recent JVM (Java 6 or later). 
It is made available as a runnable jar file with both a cross-platform SAT solver
([Sat4j](http://www.sat4j.org/) and more efficient native SAT solvers ([minisat](http://minisat.se), [lingeling/plingeling](http://fmv.jku.at/lingeling/), [glucose](http://www.labri.fr/perso/lsimon/glucose/)).

Note however that starting with macOS High Sierra, it is necessary to install a dedicated
JVM to run Alloy on macOS. A `.pkg` file is provided for that purpose.

# TL;DR

Checkout the project and type ./gradlew. You find the executable JAR in org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar after the build has finished.

     $ java version           # requires 1.8 (and NOT 1.9, gradle does not run on 1.9)
     java version "1.8.0_144"
     Java(TM) SE Runtime Environment (build 1.8.0_144-b01)
     Java HotSpot(TM) 64-Bit Server VM (build 25.144-b01, mixed model
     $ git clone git@github.com:AlloyTools/org.alloytools.alloy.git
     $ cd org.alloytools.alloy
     $ ./gradlew build
     $ java -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar
     # opens GUI

Note: if you are behind a proxy, the call to `gradlew` is likely to fail, unless you pass it further options about the http and https proxies (and possibly your login and password on this proxy). There are several ways to pass these options, a simple one is to type (replace the `XXXXX`'s by the adequate settings):

     $ ./gradlew -Dhttps.proxyHost=XXXXX -Dhttp.proxyHost=XXXXX -Dhttp.proxyPort=XXXXX \
          -Dhttps.proxyPort=XXXXX -Dhttp.proxyUser=XXXXX -Dhttp.proxyPassword=XXXXX \
          -Dhttps.proxyUser=XXXXX -Dhttps.proxyPassword=XXXXX \
          build

## Building Alloy

The Alloy build is using a _bnd workspace_ setup using a maven layout. This means it can be build  with Gradle and  the Eclipse IDE for interactive development. Projects are setup to continuously deliver the executable.

### Projects

The workspace is divided into a number of projects:

* [cnf](cnf) – Setup directory. Dependencies are specified in [cnf/central.xml] using the maven POM layout
* [org.alloytools.alloy.application](org.alloytools.alloy.application) – Main application code includes the parser, ast, visualiser, and application code
* [org.alloytools.alloy.dist](org.alloytools.alloy.dist) – Project to create the distribution executable JAR
* [org.alloytools.alloy.extra](org.alloytools.alloy.extra) – Models and examples
* [org.alloytools.kodkod.core](org.alloytools.kodkod.core) – Kodkod without native code
* [org.alloytools.kodkod.native](org.alloytools.kodkod.native) – The native code libraries for kodkod

### Relevant Project files

This workspace uses bnd. This means that the following have special meaning:

* [cnf/build.xml](cnf/build.xml) – Settings shared between projects
* ./bnd.bnd – Settings for a project. This file will _drag_ in code in a JAR.
* [cnf/central.xml](cnf/central.xml) – Dependencies from maven central

### Eclipse

The workspace is setup for interactive development in Eclipse with the Bndtools plugin. Download [Eclipse](https://www.eclipse.org/downloads/) and install it. You can then `Import` existing projects from the Git workspace. You should be asked to install Bndtools from the market place. You can also install Bndtools directly from the [Eclipse Market](https://marketplace.eclipse.org/content/bndtools) place (see `Help/Marketplace` and search for `Bndtools`). 

Bndtools will continuously create the final executable. The projects are setup to automatically update when a downstream project changes.

### IntelliJ IDEA (Ultimate Edition only)

Ensure you have the [Osmorc] plugin is enabled, as this plugin is needed for
Bndtools support. It should be enabled by default.

1. Choose "Import Project"
2. Select the `org.alloytools.alloy` directory.
3. Choose "Import project from external model: Bnd/Bndtools" and click "Next"
4. For "Select Bnd/Bndtools project to import", all projects should be checked
   by default, click "Next"
5. For project SDK, Choose "1.8", Click Finish

Note: do *not* link the Gradle project, as this will prevent you from running
Alloy within IDEA.

To run the Alloy GUI within IDEA, navigate to
org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleGUI and run the SimpleGUI class.

[Osmorc]: https://plugins.jetbrains.com/plugin/1816-osmorc


### Gradle 

In the root of this workspace type `./gradlew`. This is a script that will download the correct version of gradle and run the build scripts. For settings look at [gradle.properties] and [settings.gradle].

### Continuous Integration

The workspace is setup to build after every commit using Travis. It releases snapshots to `https://oss.sonatype.org/content/repositories/snapshots/org/alloytools/` for every CI build on Travis.

### Building the DMG file for OSX systems

Currently only the executable jar in org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar is build. In the `org.alloytools.alloy.dist` project, run `../gradlew macos`. This will leave the PKG file in `target/bundle`.

## CONTRIBUTIONS

Please read the [CONTRIBUTING](CONTRIBUTING.md) to understand how you can contribute.

[javapackager]: https://docs.oracle.com/javase/8/docs/technotes/guides/deploy/packager.html
=======
**Edit a file, create a new file, and clone from Bitbucket in under 2 minutes**

When you're done, you can delete the content in this README and update the file with details for others getting started with your repository.

*We recommend that you open this README in another tab as you perform the tasks below. You can [watch our video](https://youtu.be/0ocf7u76WSo) for a full demo of all the steps in this tutorial. Open the video in a new tab to avoid leaving Bitbucket.*

---

## Edit a file

You’ll start by editing this README file to learn how to edit a file in Bitbucket.

1. Click **Source** on the left side.
2. Click the README.md link from the list of files.
3. Click the **Edit** button.
4. Delete the following text: *Delete this line to make a change to the README from Bitbucket.*
5. After making your change, click **Commit** and then **Commit** again in the dialog. The commit page will open and you’ll see the change you just made.
6. Go back to the **Source** page.

---

## Create a file

Next, you’ll add a new file to this repository.

1. Click the **New file** button at the top of the **Source** page.
2. Give the file a filename of **contributors.txt**.
3. Enter your name in the empty file space.
4. Click **Commit** and then **Commit** again in the dialog.
5. Go back to the **Source** page.

Before you move on, go ahead and explore the repository. You've already seen the **Source** page, but check out the **Commits**, **Branches**, and **Settings** pages.

---

## Clone a repository

Use these steps to clone from SourceTree, our client for using the repository command-line free. Cloning allows you to work on your files locally. If you don't yet have SourceTree, [download and install first](https://www.sourcetreeapp.com/). If you prefer to clone from the command line, see [Clone a repository](https://confluence.atlassian.com/x/4whODQ).

1. You’ll see the clone button under the **Source** heading. Click that button.
2. Now click **Check out in SourceTree**. You may need to create a SourceTree account or log in.
3. When you see the **Clone New** dialog in SourceTree, update the destination path and name if you’d like to and then click **Clone**.
4. Open the directory you just created to see your repository’s files.

Now that you're more familiar with your Bitbucket repository, go ahead and add a new file locally. You can [push your change back to Bitbucket with SourceTree](https://confluence.atlassian.com/x/iqyBMg), or you can [add, commit,](https://confluence.atlassian.com/x/8QhODQ) and [push from the command line](https://confluence.atlassian.com/x/NQ0zDQ).
