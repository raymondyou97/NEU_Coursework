package services;

import models.FrequentlyAskedQuestion;
import repositories.FrequentlyAskedQuestionRepository;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.bind.annotation.CrossOrigin;

import java.util.List;

import models.FrequentlyAskedAnswer;
import repositories.FrequentlyAskedAnswerRepository;

@RestController
@CrossOrigin(origins = "*")
public class FrequentlyAskedAnswerService {

    @Autowired
    FrequentlyAskedAnswerRepository faaRepository;

    @Autowired
    FrequentlyAskedQuestionRepository faqRepository;

    @GetMapping("/api/faas")
    public List<FrequentlyAskedAnswer> findAllFrequentlyAskedAnswers() {
        return faaRepository.getAllFrequentlyAskedAnswers();
    }

    @GetMapping("/api/faas/{faaId}")
    public FrequentlyAskedAnswer findFrequentlyAskedAnswerById(@PathVariable("faaId") Integer id) {
        return faaRepository.findFrequentlyAskedAnswerById(id);
    }

    @PostMapping("/api/faqs/{faqId}/faas")
    public FrequentlyAskedAnswer createFrequentlyAskedAnswer(@PathVariable("faqId") Integer id,
            @RequestBody FrequentlyAskedAnswer faa) {
        FrequentlyAskedQuestion faq = faqRepository.findFaqById(id);
        faa.setFrequentlyAskedQuestion(faq);
        return faaRepository.save(faa);
    }

    @PutMapping("/api/faas/{faaId}")
    public FrequentlyAskedAnswer updateFrequentlyAskedAnswer(@PathVariable("faaId") Integer id,
            @RequestBody FrequentlyAskedAnswer faaUpdates) {
        FrequentlyAskedAnswer faa = faaRepository.findFrequentlyAskedAnswerById(id);
        faa.setAnswer(faaUpdates.getAnswer());
        return faaRepository.save(faa);
    }

    @DeleteMapping("/api/faas/{faaId}")
    public void deleteFrequentlyAskedAnswer(@PathVariable("faaId") Integer id) {
        faaRepository.deleteById(id);
    }
}
