@file:Suppress("UnstableApiUsage")

plugins {
    kotlin("multiplatform") version "2.2.0"
}

group = "com.sschr15"
version = "0.4.0"

repositories {
    mavenCentral()
}

kotlin {
    explicitApi()

    jvm()
    jvmToolchain(17)

    listOf(
        linuxX64(),
        linuxArm64(),
        macosX64(),
        mingwX64()
    ).forEach {
        it.compilations.getByName("main") {
            cinterops {
                val z3 by creating {
                    defFile("src/nativeInterop/cinterop/z3.def")
                    includeDirs.allHeaders("headers")
                }
            }
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
