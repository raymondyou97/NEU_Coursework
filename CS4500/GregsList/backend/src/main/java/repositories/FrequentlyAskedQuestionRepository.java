package repositories;

import models.FrequentlyAskedAnswer;
import models.FrequentlyAskedQuestion;
import java.util.List;
import org.springframework.data.domain.Page;
import org.springframework.data.domain.Pageable;
import org.springframework.data.jpa.repository.JpaRepository;

import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;

public interface FrequentlyAskedQuestionRepository extends JpaRepository<FrequentlyAskedQuestion, Integer> {
        @Query(value = "SELECT faq FROM FrequentlyAskedQuestion faq WHERE faq.id=:id")
        public FrequentlyAskedQuestion findFaqById(@Param("id") Integer id);

        @Query(value = "SELECT faq FROM FrequentlyAskedQuestion faq")
        public List<FrequentlyAskedQuestion> getAllFaqs(Pageable p);

        @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa WHERE faa.frequentlyAskedQuestion=:faqId")
        public List<FrequentlyAskedAnswer> findAllFaasForFaq(@Param("faqId") Integer faqId);

        @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa WHERE faa.user=:providerId "
                        + "AND faa.frequentlyAskedQuestion=:faqId")
        public List<FrequentlyAskedAnswer> findAllFaasForFaqByProvider(@Param("faqId") Integer faqId,
                        @Param("providerId") Integer providerId);

        @Query(value = "SELECT faq FROM FrequentlyAskedQuestion faq WHERE faq.title LIKE :t AND faq.question LIKE :q")
        public Page<FrequentlyAskedQuestion> getFAQs(@Param("t") String title, @Param("q") String question,
                        Pageable pageable);
}
