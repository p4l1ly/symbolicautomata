#include <jni.h>
#include <iostream>

#include <automata-safa-capnp/SeparatedAfa.capnp.h>
#include <automata-safa-capnp/SeparatedAfaRpc.capnp.h>
#include <automata-safa-capnp/LoadedModelRpc.capnp.h>
#include <capnp/ez-rpc.h>
#include <capnp/pointer-helpers.h>
#include <capnp/arena.h>
#include <kj/thread.h>

#include "boolafa_BoolAfa.h"

namespace schema = automata_safa_capnp::separated_afa;
namespace rpcschema = automata_safa_capnp::rpc::separated_afa;
namespace rpc = automata_safa_capnp::rpc;

JavaVM *jvm;
JNIEnv *env;
jclass BoolAfa;
jclass ByteBuffer;
jmethodID BoolAfa_init;
jmethodID BoolAfa_solve;
jmethodID BoolAfa_getTime;
jmethodID BoolAfa_getStatus;
jmethodID BoolAfa_pause;
jmethodID BoolAfa_resume;
jmethodID BoolAfa_cancel;

class ControlImpl final: public rpc::ModelChecking::Control::Server {
    jobject afa;

public:
    ControlImpl(jobject afa_) : afa(afa_) {}

    kj::Promise<void> pause(PauseContext context) override {
        setStatus(
            context.getResults().getOldStatus(),
            env->CallIntMethod(afa, BoolAfa_pause)
        );
        return kj::READY_NOW;
    }

    kj::Promise<void> resume(ResumeContext context) override {
        setStatus(
            context.getResults().getOldStatus(),
            env->CallIntMethod(afa, BoolAfa_resume)
        );
        return kj::READY_NOW;
    }

    kj::Promise<void> cancel(CancelContext context) override {
        setStatus(
            context.getResults().getOldStatus(),
            env->CallIntMethod(afa, BoolAfa_cancel)
        );
        return kj::READY_NOW;
    }

    kj::Promise<void> getStatus(GetStatusContext context) override {
        setStatus(
            context.getResults().getStatus(),
            env->CallIntMethod(afa, BoolAfa_getStatus)
        );
        return kj::READY_NOW;
    }

private:
    void setStatus(rpc::ModelChecking::Status::Builder status, int state) {
        status.setTime(env->CallIntMethod(afa, BoolAfa_getTime));
        switch(state) {
            case 0:
                status.setState(rpc::ModelChecking::Status::State::RUNNING); return;
            case 3:
                status.setState(rpc::ModelChecking::Status::State::INIT); return;
            case 2:
                status.setState(rpc::ModelChecking::Status::State::CANCELLED); return;
            case 1:
                status.setState(rpc::ModelChecking::Status::State::PAUSED); return;
        }
    }
};

class ModelCheckingImpl final: public rpc::ModelChecking::Server {
    jobject afa;

public:
    ModelCheckingImpl(jobject afa) : afa(afa) {}

    kj::Promise<void> solve(SolveContext context) override {
        kj::MutexGuarded<kj::Maybe<const kj::Executor&>> executor;
        kj::Own<kj::PromiseFulfiller<void>> fulfiller;

        kj::Thread([&]() noexcept {
            kj::EventLoop loop;
            kj::WaitScope scope(loop);
            *executor.lockExclusive() = kj::getCurrentThreadExecutor();

            auto paf = kj::newPromiseAndFulfiller<void>();
            fulfiller = kj::mv(paf.fulfiller);
            paf.promise.wait(scope);
        }).detach();

        const kj::Executor *exec;
        {
            auto lock = executor.lockExclusive();
            lock.wait([&](kj::Maybe<const kj::Executor&> value) {
                return value != nullptr;
            });
            exec = &KJ_ASSERT_NONNULL(*lock);
        }

        rpc::ModelChecking::SolveResults::Builder result = context.getResults();

        return exec->executeAsync(
            [this, result, fulfiller{kj::mv(fulfiller)}]() mutable {
                JNIEnv *env;
                jvm->AttachCurrentThread((void**)&env, NULL);
                jint r = env->CallIntMethod(afa, BoolAfa_solve);
                switch(r) {
                    case 0:
                        result.setResult(rpc::ModelChecking::Result::EMPTY); break;
                    case 1:
                        result.setResult(rpc::ModelChecking::Result::NONEMPTY); break;
                    case 2:
                        result.setResult(rpc::ModelChecking::Result::CANCELLED); break;
                }
                result.setTime(env->CallIntMethod(afa, BoolAfa_getTime));

                fulfiller->fulfill();
            }
        );
    }

    kj::Promise<void> getControl(GetControlContext context) override {
        context.getResults().setControl(kj::heap<ControlImpl>(afa));
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

        context.getResults().setLoadedModel(kj::heap<ModelCheckingImpl>(loaded_afa));

        return kj::READY_NOW;
    }
};

JNIEXPORT void JNICALL Java_boolafa_BoolAfa_runRpcServer(JNIEnv *env_, jclass BoolAfa_)
{
    env = env_;
    env->GetJavaVM(&jvm);
    BoolAfa = BoolAfa_;
    BoolAfa_init = env->GetMethodID(
        BoolAfa, "<init>", "([Ljava/nio/ByteBuffer;IIIIS)V");
    BoolAfa_solve = env->GetMethodID(BoolAfa, "solve", "()I");
    BoolAfa_getTime = env->GetMethodID(BoolAfa, "getTime", "()I");
    BoolAfa_getStatus = env->GetMethodID(BoolAfa, "getStatus", "()I");
    BoolAfa_pause = env->GetMethodID(BoolAfa, "pause", "()I");
    BoolAfa_resume = env->GetMethodID(BoolAfa, "resume", "()I");
    BoolAfa_cancel = env->GetMethodID(BoolAfa, "cancel", "()I");
    ByteBuffer = env->FindClass("java/nio/ByteBuffer");

    capnp::EzRpcServer server(kj::heap<LoaderImpl>(), "0.0.0.0", 4000);
    auto& waitScope = server.getWaitScope();
    kj::NEVER_DONE.wait(waitScope);
}
