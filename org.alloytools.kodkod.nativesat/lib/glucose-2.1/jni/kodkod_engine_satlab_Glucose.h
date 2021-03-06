/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class kodkod_engine_satlab_Glucose */

#ifndef _Included_kodkod_engine_satlab_Glucose
#define _Included_kodkod_engine_satlab_Glucose
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_Glucose_make
  (JNIEnv *, jclass);

/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Glucose_free
  (JNIEnv *, jobject, jlong);

/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Glucose_addVariables
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose_addClause
  (JNIEnv *, jobject, jlong, jintArray);

/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose_solve
  (JNIEnv *, jobject, jlong);

/*
 * Class:     kodkod_engine_satlab_Glucose
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose_valueOf
  (JNIEnv *, jobject, jlong, jint);

#ifdef __cplusplus
}
#endif
#endif
