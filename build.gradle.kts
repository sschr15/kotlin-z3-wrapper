@file:Suppress("UnstableApiUsage")

import org.jetbrains.kotlin.daemon.common.toHexString
import java.net.URI
import java.security.MessageDigest

plugins {
    kotlin("multiplatform") version "2.2.0"
    `maven-publish`
}

group = "com.sschr15.z3kt"
version = "0.5.0"

repositories {
    mavenCentral()
}

val z3Downloads = mapOf(
    "linuxX64" to "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-glibc-2.39.zip",
    "linuxArm64" to "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-arm64-glibc-2.34.zip",
    "macosX64" to "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-osx-13.7.6.zip",
    "macosArm64" to "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-arm64-osx-13.7.6.zip",
    "mingwX64" to "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-win.zip",
    //TODO mingwArm64 when Kotlin supports it
)

val z3Shas = mapOf(
    "linuxX64" to "85d2da1bf440fca3288874c2a06e23f96d09befcc21b5a7489fe0fa40444e685",
    "linuxArm64" to "13ef5c1f91cae46c3de493cd1f98954331e4e7d0850bbbcf208b818d452bf99b",
    "macosX64" to "2c0fb34703660cb3c182c84d702674f52b56f9454cdc6c30d58611a1c2d69851",
    "macosArm64" to "fdc797b046a8b1e030200d30c4c32724fc01be359c3ab88a47ce03655cf6efa4",
    "mingwX64" to "39c367032343b75175b1dae5bd56ed20405d28f8b87ebfeac1dd04c12bdc0269",
)

kotlin {
    explicitApi()

    jvm()
    jvmToolchain(8)

    listOf(
        linuxX64(),
        linuxArm64(),
        macosX64(),
        macosArm64(),
        mingwX64()
    ).forEach { target ->
        val z3Dir = layout.buildDirectory.dir("z3/${target.targetName}").get().asFile

        val genData = tasks.register<ProcessResources>("${target.targetName}Defs") {
            outputs.upToDateWhen { false }

            from(files("src/nativeInterop/cinterop/z3.def"))
            into(z3Dir.resolve("lib"))
            expand("cinteropLibs" to z3Dir.resolve("bin").absolutePath)

            doFirst {
                val downloadUrl = z3Downloads[target.targetName] ?: error("No download URL found for target ${target.targetName}")
                val z3Zip = layout.buildDirectory.file("z3/${target.targetName}.zip").get().asFile
                val z3Sha = z3Shas[target.targetName] ?: error("No SHA found for target ${target.targetName}")
                var calculatedSha = MessageDigest.getInstance("SHA-256")
                    .digest(z3Zip.takeIf(File::isFile)?.readBytes() ?: byteArrayOf())
                    .toHexString()
                if (calculatedSha != z3Sha || !z3Zip.exists()) {
                    z3Dir.deleteRecursively()
                    z3Zip.delete()
                    z3Zip.parentFile.mkdirs()
                    println("Downloading Z3 from $downloadUrl")
                    z3Zip.writeBytes(URI.create(downloadUrl).toURL().readBytes())
                    println("Verifying checksum")
                    calculatedSha = MessageDigest.getInstance("SHA-256").digest(z3Zip.readBytes()).toHexString()
                    if (calculatedSha != z3Sha) {
                        logger.error("Checksum mismatch for Z3. Expected $z3Sha, got $calculatedSha.")
                        throw RuntimeException("Failed to verify Z3 checksum.")
                    }
                }
                if (!z3Dir.exists() || !z3Dir.resolve("bin").exists() || !z3Dir.resolve("include").exists()) {
                    println("Extracting Z3")
                    copy {
                        from(zipTree(z3Zip)) {
                            eachFile {
                                relativePath = RelativePath(true, *relativePath.segments.drop(1).toTypedArray())
                            }
                            include("**/*.h")
                            include("**/*.a")
                            include("**/*.dll")
                            include("**/*.dylib")
                            include("**/*.so")
                        }
                        into(z3Dir)
                    }

                    println("Adding logging function for cinterop issues")
                    z3Dir.resolve("include/z3_api.h").appendText("""
                        inline void Z3_API Z3_set_error_handler_b(Z3_context c, void (*f)(Z3_context c, Z3_error_code e)) {
                            Z3_set_error_handler(c, f);
                        }
                    """.trimIndent())

                    println("Finished building Z3 for target ${target.targetName}")
                }
            }
        }
 
        target.compilations.getByName("main") {
            cinterops {
                val z3 by creating {
                    defFile(genData.get().outputs.files.singleFile.resolve("z3.def"))
                    includeDirs.allHeaders(z3Dir.resolve("include"))
                    compilerOpts("-I${z3Dir.resolve("include").absolutePath}")
                }
            }
        }

        tasks.getByName("cinteropZ3${target.targetName.replaceFirstChar { c -> c.uppercase() }}") {
            dependsOn(genData)
        }
    }

    compilerOptions {
        optIn.addAll(
            "kotlin.contracts.ExperimentalContracts",
            "kotlinx.cinterop.ExperimentalForeignApi",
        )
        freeCompilerArgs.addAll(
            "-Xcontext-parameters",
            "-Xexpect-actual-classes",
        )
    }

    sourceSets {
        commonTest {
            dependencies {
                implementation(kotlin("test"))
            }
        }
        jvmMain {
            dependencies {
                implementation(files("com.microsoft.z3.jar"))
            }
        }
    }
}

publishing {
    repositories {
        mavenLocal()
    }
}
