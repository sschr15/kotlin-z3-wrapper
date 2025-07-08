@file:Suppress("UnstableApiUsage")

import org.jetbrains.kotlin.gradle.utils.extendsFrom

plugins {
    kotlin("jvm") version "2.2.0"
}

group = "com.sschr15"
version = "0.4.0"

repositories {
    mavenCentral()
}

val include by configurations.registering
configurations.implementation.extendsFrom(include)

dependencies {
    include(files("com.microsoft.z3.jar"))
    testImplementation(kotlin("test"))
}

tasks {
    jar {
        from(include.get().map { if (it.isDirectory) it else zipTree(it) })
    }

    test {
        useJUnitPlatform()
    }

    val sourcesJar by registering(Jar::class) {
        dependsOn(classes)
        archiveClassifier = "sources"
        from(sourceSets.main.get().allSource) {
            exclude("natives/**")
        }
    }

    val thinJar by registering(Jar::class) {
        dependsOn(classes)
        archiveClassifier = "thin"
        from(sourceSets.main.get().output) {
            exclude("natives/**")
        }
        from(include.get().map { if (it.isDirectory) it else zipTree(it) })
    }

    assemble {
        dependsOn(sourcesJar)
        dependsOn(thinJar)
    }
}

kotlin {
    jvmToolchain(17)
    explicitApi()

    compilerOptions { 
        optIn.add("kotlin.contracts.ExperimentalContracts")
        freeCompilerArgs.add("-Xcontext-parameters")
    }
}
