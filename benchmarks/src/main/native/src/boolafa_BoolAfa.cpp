#include <jni.h>
#include <iostream>

#include <automata-safa-capnp/SeparatedAfa.capnp.h>
#include <automata-safa-capnp/SeparatedAfaRpc.capnp.h>
#include <capnp/ez-rpc.h>
#include <capnp/pointer-helpers.h>
#include <capnp/arena.h>

#include "boolafa_BoolAfa.h"

namespace schema = automata_safa_capnp::separated_afa;
namespace rpcschema = automata_safa_capnp::separated_afa_rpc;

JNIEnv *env;
jclass BoolAfa;
jclass ByteBuffer;
jmethodID BoolAfa_init;
jmethodID BoolAfa_is_empty;

class LoadedModelImpl final: public rpcschema::LoadedModel::Server {
    jobject afa;

public:
    LoadedModelImpl(jobject afa) : afa(afa) {}

    kj::Promise<void> solve(SolveContext context) override {
        jboolean is_empty = env->CallBooleanMethod(afa, BoolAfa_is_empty);
        context.getResults().setEmpty(is_empty);
        return kj::READY_NOW;
    }
};

class LoaderImpl final: public rpcschema::Loader::Server {
public:
    kj::Promise<void> load(LoadContext context) override {
        schema::SeparatedAfa::Reader afa = context.getParams().getModel();

        // Get the struct's low level environment
        capnp::_::StructReader reader =
            capnp::_::PointerHelpers<schema::SeparatedAfa>::getInternalReader(afa);
        capnp::_::SegmentReader* segment = reader.getSegment();
        capnp::_::Arena* arena = segment->getArena();

        // Get segment count of the arena
        int count;
        for(count = 0;; count++) {
            if (arena->tryGetSegment(capnp::_::SegmentId(count)) == NULL) break;
        }

        // Fill java array with segment pointers
        jobjectArray segments = env->NewObjectArray(count, ByteBuffer, NULL);

        for(int i = 0; i < count; i++) {
            capnp::_::SegmentReader* seg = arena->tryGetSegment(capnp::_::SegmentId(i));

            jobject segbuf = env->NewDirectByteBuffer(
                const_cast<capnp::word *>(seg->getStartPtr()),
                seg->getSize() * capnp::BYTES_PER_WORD / capnp::BYTES
            );

            env->SetObjectArrayElement(segments, i, segbuf); 
        }

        // Get location of the struct in the message
        int segment_id = segment->getSegmentId().value;
        int data_size_bits = reader.getDataSectionSize();
        int pointer_count = reader.getPointerSectionSize();
        int data_pos =
            segment->getOffsetTo((capnp::word*)reader.getLocation()) / capnp::WORDS;
        int pointer_pos = data_pos + (data_size_bits / capnp::BITS_PER_WORD) ;
        if (data_size_bits % capnp::BITS_PER_WORD) pointer_pos++;

        // Pass the capnp arena with the struct's location to Java
        jobject loaded_afa = env->NewObject(
            BoolAfa, BoolAfa_init,
            segments, segment_id, data_pos, pointer_pos, data_size_bits, pointer_count
        );

        context.getResults().setLoadedModel(kj::heap<LoadedModelImpl>(loaded_afa));

        return kj::READY_NOW;
    }
};

JNIEXPORT void JNICALL Java_boolafa_BoolAfa_runRpcServer(JNIEnv *env_, jclass BoolAfa_)
{
    env = env_;
    BoolAfa = BoolAfa_;
    BoolAfa_init = env->GetMethodID(
        BoolAfa, "<init>", "([Ljava/nio/ByteBuffer;IIIIS)V");
    BoolAfa_is_empty = env->GetMethodID(BoolAfa, "is_empty", "()Z");
    ByteBuffer = env->FindClass("java/nio/ByteBuffer");

    capnp::EzRpcServer server(kj::heap<LoaderImpl>(), "0.0.0.0", 4000);
    auto& waitScope = server.getWaitScope();
    kj::NEVER_DONE.wait(waitScope);
}
