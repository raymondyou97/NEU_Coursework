package services;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.data.domain.PageRequest;
import org.springframework.data.domain.Pageable;
import org.springframework.data.domain.Page;
import org.springframework.web.bind.annotation.*;

import java.util.List;

import models.FrequentlyAskedAnswer;
import models.FrequentlyAskedQuestion;
import repositories.FrequentlyAskedAnswerRepository;
import repositories.FrequentlyAskedQuestionRepository;

@RestController
@CrossOrigin(origins = "*")
public class FrequentlyAskedQuestionService {

    @Autowired
    FrequentlyAskedQuestionRepository faqRepository;

    @Autowired
    FrequentlyAskedAnswerService faaService;

    @Autowired
    FrequentlyAskedAnswerRepository faaRepository;

    @GetMapping("/api/faqs")
    public Page<FrequentlyAskedQuestion> findAllFrequentlyAskedQuestions(
            @RequestParam(name = "page", required = false, defaultValue = "0") Integer page,
            @RequestParam(name = "count", required = false) Integer count,
            @RequestParam(name = "titleFilter", required = false, defaultValue = "") String titleFilter,
            @RequestParam(name = "questionFilter", required = false, defaultValue = "") String questionFilter) {

        Pageable p = Pageable.unpaged();

        if (count != null) {
            p = PageRequest.of(page, count);
        }

        String titleFuzzy = "%" + titleFilter + "%";
        String questionFuzzy = "%" + questionFilter + "%";

        return faqRepository.getFAQs(titleFuzzy, questionFuzzy, p);
    }

    @GetMapping("/api/faqs/{faqId}")
    public FrequentlyAskedQuestion findFrequentlyAskedQuestionById(@PathVariable("faqId") Integer id) {
        return faqRepository.findFaqById(id);
    }

    @PostMapping("/api/faqs")
    public FrequentlyAskedQuestion createFrequentlyAskedQuestion(@RequestBody FrequentlyAskedQuestion faq) {
        return faqRepository.save(faq);
    }

    @PutMapping("/api/faqs/{faqId}")
    public FrequentlyAskedQuestion updateFrequentlyAskedQuestion(@PathVariable("faqId") Integer id,
            @RequestBody FrequentlyAskedQuestion faqUpdates) {
        FrequentlyAskedQuestion faq = faqRepository.findFaqById(id);
        faq.setTitle(faqUpdates.getTitle());
        faq.setQuestion(faqUpdates.getQuestion());
        // faq.setAnswers(faqUpdates.getAnswers());
        return faqRepository.save(faq);
    }

    @DeleteMapping("/api/faqs/{faqId}")
    public void deleteFrequentlyAskedQuestion(@PathVariable("faqId") Integer id) {
        faqRepository.deleteById(id);
    }

    @GetMapping("api/faqs/{faqId}/faas")
    public void getFaasFromFaqId(@PathVariable("faqId") Integer id) {
        faqRepository.findAllFaasForFaq(id);
    }

    @PostMapping("api/faqs/{faqId}/faas/{faaId}")
    public void createFaaToFaqRelationship(@PathVariable("faqId") Integer faqId, @PathVariable("faaId") Integer faaId) {
        FrequentlyAskedQuestion faq = faqRepository.findFaqById(faqId);
        List<FrequentlyAskedAnswer> answers = faq.getAnswers();
        answers.add(faaService.findFrequentlyAskedAnswerById(faaId));
        faq.setAnswers(answers);
        faqRepository.save(faq);
    }

    @DeleteMapping("api/faqs/{faqId}/faas/{faaId}")
    public void deleteFaaToFaqRelationship(@PathVariable("faqId") Integer faqId, @PathVariable("faaId") Integer faaId) {
        FrequentlyAskedQuestion faq = faqRepository.findFaqById(faqId);
        List<FrequentlyAskedAnswer> answers = faq.getAnswers();
        answers.remove(faaService.findFrequentlyAskedAnswerById(faaId));
        faq.setAnswers(answers);
        faqRepository.save(faq);
        faaRepository.deleteById(faaId);
    }

}
